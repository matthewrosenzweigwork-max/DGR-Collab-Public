import SharpSymmetricLSI.Infra.SmoothWeakGrad

/-!
# Classical `C¹` calculus on the torus (for the Gross lemma on `(𝕋^d)^N`)

`C1T f`: the periodic lift `f ∘ liftT` is `C¹`. The classical partial derivative is represented by
`dT f k y = ∂_k (f ∘ liftT) (secT y)` (the representative of the weak gradient in
`SharpSymmetricLSI.Infra.SmoothWeakGrad`), so no discontinuity of the box representative enters.
-/

open MeasureTheory SharpLSI

namespace SharpLSI.FL.Gross

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `f` is `C¹` on the torus (its periodic lift is). -/
def C1T (f : UnitAddTorus ι → ℝ) : Prop := ContDiff ℝ 1 (f ∘ liftT)

/-- The classical partial derivative `∂_k f` (box representative `secT`). -/
noncomputable def dT (f : UnitAddTorus ι → ℝ) (k : ι) (y : UnitAddTorus ι) : ℝ :=
  fderiv ℝ (f ∘ liftT) (secT y) (Pi.single k 1)

lemma dT_liftT (f : UnitAddTorus ι → ℝ) (x : ι → ℝ) (k : ι) :
    dT f k (liftT x) = fderiv ℝ (f ∘ liftT) x (Pi.single k 1) := by
  unfold dT; rw [fderiv_lift_secT]

lemma C1T.eq_comp_secT {f : UnitAddTorus ι → ℝ} : f = (f ∘ liftT) ∘ secT := by
  funext y; simp [Function.comp, liftT_secT]

lemma C1T.measurable {f : UnitAddTorus ι → ℝ} (hf : C1T f) : Measurable f := by
  rw [C1T.eq_comp_secT (f := f)]
  exact hf.continuous.measurable.comp measurable_secT

lemma secT_mem_Icc (y : UnitAddTorus ι) : secT y ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
  intro i _
  have : (AddCircle.measurableEquivIoc 1 0 (y i) : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
    (AddCircle.measurableEquivIoc 1 0 (y i)).2
  simpa [secT] using Set.Ioc_subset_Icc_self (by simpa using this)

lemma C1T.bounded {f : UnitAddTorus ι → ℝ} (hf : C1T f) : ∃ K, ∀ y, |f y| ≤ K := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨K, hK'⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  refine ⟨K, fun y => ?_⟩
  have := hK' (secT y) (secT_mem_Icc y)
  rwa [Real.norm_eq_abs, Function.comp_apply, liftT_secT] at this

lemma C1T.continuous_fderiv_apply {f : UnitAddTorus ι → ℝ} (hf : C1T f) (k : ι) :
    Continuous fun x => fderiv ℝ (f ∘ liftT) x (Pi.single k 1) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma C1T.dT_measurable {f : UnitAddTorus ι → ℝ} (hf : C1T f) (k : ι) : Measurable (dT f k) :=
  (hf.continuous_fderiv_apply k).measurable.comp measurable_secT

lemma C1T.dT_bounded {f : UnitAddTorus ι → ℝ} (hf : C1T f) (k : ι) : ∃ K, ∀ y, |dT f k y| ≤ K := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨K, hK'⟩ := hK.exists_bound_of_continuousOn (hf.continuous_fderiv_apply k).continuousOn
  exact ⟨K, fun y => by simpa [Real.norm_eq_abs, dT] using hK' (secT y) (secT_mem_Icc y)⟩

lemma C1T.comp {f : UnitAddTorus ι → ℝ} (hf : C1T f) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    C1T (ψ ∘ f) := hψ.comp hf

lemma dT_comp {f : UnitAddTorus ι → ℝ} (hf : C1T f) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (k : ι) (y : UnitAddTorus ι) : dT (ψ ∘ f) k y = deriv ψ (f y) * dT f k y := by
  unfold dT
  have hg : DifferentiableAt ℝ (f ∘ liftT) (secT y) := (hf.differentiable one_ne_zero) _
  have hψd : HasDerivAt ψ (deriv ψ ((f ∘ liftT) (secT y))) ((f ∘ liftT) (secT y)) :=
    ((hψ.differentiable one_ne_zero) _).hasDerivAt
  have := hψd.comp_hasFDerivAt (secT y) hg.hasFDerivAt
  have e : (ψ ∘ f) ∘ liftT = ψ ∘ (f ∘ liftT) := rfl
  rw [e, this.fderiv]
  simp [Function.comp, liftT_secT]

lemma C1T.add {f g : UnitAddTorus ι → ℝ} (hf : C1T f) (hg : C1T g) : C1T (fun y => f y + g y) :=
  ContDiff.add hf hg

lemma C1T.const_mul {f : UnitAddTorus ι → ℝ} (hf : C1T f) (c : ℝ) : C1T (fun y => c * f y) :=
  ContDiff.const_smul c hf

lemma C1T.const (c : ℝ) : C1T (fun _ : UnitAddTorus ι => c) := contDiff_const

lemma C1T.sum {κ : Type*} (s : Finset κ) {g : κ → UnitAddTorus ι → ℝ} (c : κ → ℝ)
    (hg : ∀ i ∈ s, C1T (g i)) : C1T (fun y => ∑ i ∈ s, c i * g i y) := by
  unfold C1T
  have : ((fun y => ∑ i ∈ s, c i * g i y) ∘ liftT) = fun x => ∑ i ∈ s, c i * (g i ∘ liftT) x := rfl
  rw [this]
  exact ContDiff.sum fun i hi => (hg i hi).const_smul (c i)

lemma dT_sum {κ : Type*} (s : Finset κ) {g : κ → UnitAddTorus ι → ℝ} (c : κ → ℝ)
    (hg : ∀ i ∈ s, C1T (g i)) (k : ι) (y : UnitAddTorus ι) :
    dT (fun y => ∑ i ∈ s, c i * g i y) k y = ∑ i ∈ s, c i * dT (g i) k y := by
  unfold dT
  have h : HasFDerivAt (fun x => ∑ i ∈ s, c i * (g i ∘ liftT) x)
      (∑ i ∈ s, c i • fderiv ℝ (g i ∘ liftT) (secT y)) (secT y) := by
    refine HasFDerivAt.fun_sum fun i hi => ?_
    exact ((hg i hi).differentiable one_ne_zero (secT y)).hasFDerivAt.const_mul (c i)
  have e : ((fun y => ∑ i ∈ s, c i * g i y) ∘ liftT) = fun x => ∑ i ∈ s, c i * (g i ∘ liftT) x := rfl
  rw [e, h.fderiv]
  simp

/-- The weak gradient of a `C¹` function is its classical gradient. -/
lemma weakGrad_ae_eq_dT {f : UnitAddTorus ι → ℝ} (hf : C1T f) :
    weakGrad f =ᵐ[volume] fun y k => dT f k y :=
  weakGrad_ae_eq_of_contDiff hf

end SharpLSI.FL.Gross
