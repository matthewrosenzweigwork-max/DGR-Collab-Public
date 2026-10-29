import DGPS.Variational.EquilibriumGibbs

open MeasureTheory
open scoped ENNReal RealInnerProductSpace BoundedContinuousFunction

namespace DGPS.Lipschitz

variable {d : ℕ}

section Kernel

variable (A : InteractionData d) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem centeredKernel_continuous :
    Continuous fun p : Torus d × Torus d => centeredKernel A μ p.1 p.2 := by
  have h1 := A.W_continuous
  have h2 : Continuous fun p : Torus d × Torus d => interactionConvolution A μ p.1 :=
    (continuous_interactionConvolution A μ).comp continuous_fst
  have h3 : Continuous fun p : Torus d × Torus d => interactionConvolution A μ p.2 :=
    (continuous_interactionConvolution A μ).comp continuous_snd
  exact ((h1.sub h2).sub h3).add continuous_const

omit [IsProbabilityMeasure μ] in
theorem centeredKernel_symm (x y : Torus d) : centeredKernel A μ x y = centeredKernel A μ y x := by
  unfold centeredKernel; rw [A.W_symm x y]; ring

theorem integral_centeredKernel_right (x : Torus d) :
    ∫ y, centeredKernel A μ x y ∂μ = 0 := by
  have hc := continuous_interactionConvolution A μ
  have iW : Integrable (fun y => A.W x y) μ :=
    (A.W_continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ic : Integrable (fun y => interactionConvolution A μ y) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : ∫ y, interactionConvolution A μ y ∂μ = interactionEnergy A μ := by
    rw [← interactionPairing_self, interactionPairing_eq_integral]
  unfold centeredKernel
  have i1 : Integrable (fun y => A.W x y - interactionConvolution A μ x) μ :=
    iW.sub (integrable_const _)
  have i2 : Integrable (fun y => A.W x y - interactionConvolution A μ x -
      interactionConvolution A μ y) μ := i1.sub ic
  rw [integral_add i2 (integrable_const _), integral_sub i1 ic,
    integral_sub iW (integrable_const _), e]
  simp [interactionConvolution]

theorem centeredKernel_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ x y, |centeredKernel A μ x y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    (centeredKernel_continuous A μ).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have := hM (x, y) trivial
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- the section `y ↦ K(x,y)` as an `L²(μ)` class. -/
noncomputable def kernelSection (x : Torus d) : Lp ℝ 2 μ :=
  ContinuousMap.toLp 2 μ ℝ
    (ContinuousMap.curry (⟨_, centeredKernel_continuous A μ⟩ : C(Torus d × Torus d, ℝ)) x)

theorem continuous_kernelSection : Continuous (kernelSection A μ) :=
  (ContinuousMap.toLp 2 μ ℝ (E := ℝ)).continuous.comp
    (ContinuousMap.curry (⟨_, centeredKernel_continuous A μ⟩ : C(Torus d × Torus d, ℝ))).continuous

theorem kernelSection_ae (x : Torus d) :
    kernelSection A μ x =ᵐ[μ] fun y => centeredKernel A μ x y := by
  unfold kernelSection
  exact ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ) _ |>.trans (by exact Filter.EventuallyEq.rfl)

theorem inner_kernelSection (x : Torus d) (f : Lp ℝ 2 μ) :
    ⟪kernelSection A μ x, f⟫ = ∫ y, centeredKernel A μ x y * f y ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [kernelSection_ae A μ x] with y hy
  rw [hy]; simp [mul_comm]


omit [IsProbabilityMeasure μ] in
theorem norm_toLp_le_norm [IsProbabilityMeasure μ] (f : C(Torus d, ℝ)) :
    ‖ContinuousMap.toLp (E := ℝ) 2 μ ℝ f‖ ≤ ‖f‖ := by
  have h1 := (ContinuousMap.toLp 2 μ ℝ : C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 μ).le_opNorm f
  have h2 := ContinuousMap.toLp_norm_le (α := Torus d) (E := ℝ) (p := 2) μ (𝕜 := ℝ)
  have h3 : measureUnivNNReal μ = 1 := by simp [measureUnivNNReal]
  rw [h3] at h2
  simp at h2
  calc _ ≤ _ := h1
    _ ≤ 1 * ‖f‖ := by gcongr
    _ = ‖f‖ := one_mul _

/-- a uniform bound for the centered kernel. -/
noncomputable def kBound : ℝ := (centeredKernel_bounded A μ).choose

theorem kBound_nonneg : 0 ≤ kBound A μ := (centeredKernel_bounded A μ).choose_spec.1

theorem abs_centeredKernel_le (x y : Torus d) : |centeredKernel A μ x y| ≤ kBound A μ :=
  (centeredKernel_bounded A μ).choose_spec.2 x y

theorem norm_kernelSection_le (x : Torus d) : ‖kernelSection A μ x‖ ≤ kBound A μ := by
  unfold kernelSection
  refine (norm_toLp_le_norm μ _).trans ?_
  refine (ContinuousMap.norm_le _ (kBound_nonneg A μ)).2 fun y => ?_
  simpa [Real.norm_eq_abs] using abs_centeredKernel_le A μ x y

/-- the linear map `f ↦ (x ↦ ⟪K(x,·), f⟫)`. -/
noncomputable def TcontLin : Lp ℝ 2 μ →ₗ[ℝ] C(Torus d, ℝ) where
  toFun f := ⟨fun x => ⟪kernelSection A μ x, f⟫,
    (continuous_kernelSection A μ).inner continuous_const⟩
  map_add' f g := by ext x; simp [inner_add_right]
  map_smul' c f := by ext x; simp [inner_smul_right]

/-- the integral operator `L²(μ) → C(𝕋)`. -/
noncomputable def Tcont : Lp ℝ 2 μ →L[ℝ] C(Torus d, ℝ) :=
  (TcontLin A μ).mkContinuous (kBound A μ) (fun f => by
    refine (ContinuousMap.norm_le _ (by have := kBound_nonneg A μ; positivity)).2 fun x => ?_
    show ‖⟪kernelSection A μ x, f⟫‖ ≤ _
    exact (norm_inner_le_norm _ _).trans (by
      have := norm_kernelSection_le A μ x
      nlinarith [norm_nonneg f, norm_nonneg (kernelSection A μ x)]))

theorem Tcont_apply (f : Lp ℝ 2 μ) (x : Torus d) :
    Tcont A μ f x = ∫ y, centeredKernel A μ x y * f y ∂μ :=
  inner_kernelSection A μ x f

/-- the centered kernel operator on `L²(μ)`. -/
noncomputable def centeredOperator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ : C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 μ).comp (Tcont A μ)

/-- the centered kernel operator on `C(𝕋)`. -/
noncomputable def centeredOperatorC : C(Torus d, ℝ) →L[ℝ] C(Torus d, ℝ) :=
  (Tcont A μ).comp (ContinuousMap.toLp 2 μ ℝ : C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 μ)

theorem isCompactOperator_Tcont : IsCompactOperator (Tcont A μ) := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  set e := ContinuousMap.isometryEquivBoundedOfCompact (Torus d) ℝ
  set S : Set C(Torus d, ℝ) := Tcont A μ '' Metric.ball 0 1
  set A' : Set (Torus d →ᵇ ℝ) := e.symm ⁻¹' S
  have hval : ∀ (g : Torus d →ᵇ ℝ), g ∈ A' → ∃ h : Lp ℝ 2 μ, ‖h‖ < 1 ∧ ∀ x, g x = ⟪kernelSection A μ x, h⟫ := by
    intro g hg
    obtain ⟨h, hh, hgh⟩ := hg
    refine ⟨h, by simpa using hh, fun x => ?_⟩
    have : (e.symm g) x = Tcont A μ h x := by rw [hgh]
    exact this
  have hc : IsCompact (closure A') := by
    refine BoundedContinuousFunction.arzela_ascoli (Set.Icc (-kBound A μ) (kBound A μ)) isCompact_Icc A' ?_ ?_
    · intro g x hg
      obtain ⟨h, hh, hx⟩ := hval g hg
      rw [hx, Set.mem_Icc, ← abs_le]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have := norm_kernelSection_le A μ x
      nlinarith [norm_nonneg h, norm_nonneg (kernelSection A μ x), kBound_nonneg A μ]
    · intro x₀
      rw [Metric.equicontinuousAt_iff_pair]
      intro ε hε
      have hcont := (continuous_kernelSection A μ).continuousAt (x := x₀)
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨δ, hδ, hδ'⟩ := hcont (ε / 2) (half_pos hε)
      have key : ∀ x ∈ Metric.ball x₀ δ, ∀ i : A', dist (i.1 x) (i.1 x₀) < ε / 2 := by
        intro x hx i
        obtain ⟨h, hh, hx'⟩ := hval i.1 i.2
        rw [hx' x, hx' x₀, Real.dist_eq, ← inner_sub_left]
        have h1 := hδ' (Metric.mem_ball.1 hx)
        rw [dist_eq_norm] at h1
        calc |⟪kernelSection A μ x - kernelSection A μ x₀, h⟫|
            ≤ ‖kernelSection A μ x - kernelSection A μ x₀‖ * ‖h‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖kernelSection A μ x - kernelSection A μ x₀‖ * 1 := by
              gcongr
          _ < ε / 2 := by rw [mul_one]; exact h1
      refine ⟨Metric.ball x₀ δ, Metric.ball_mem_nhds _ hδ, fun x hx x' hx' i => ?_⟩
      calc dist (i.1 x) (i.1 x') ≤ dist (i.1 x) (i.1 x₀) + dist (i.1 x') (i.1 x₀) := dist_triangle_right _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (key x hx i) (key x' hx' i)
        _ = ε := add_halves ε
  have : closure S = e ⁻¹' closure A' := by
    have h1 : e.toHomeomorph ⁻¹' closure A' = closure (e.toHomeomorph ⁻¹' A') :=
      e.toHomeomorph.preimage_closure A'
    have h2 : e.toHomeomorph ⁻¹' A' = S := by ext f; simp [A']
    rw [show (⇑e ⁻¹' closure A') = e.toHomeomorph ⁻¹' closure A' from rfl, h1, h2]
  rw [this]
  exact e.toHomeomorph.isCompact_preimage.2 hc


theorem isCompactOperator_centeredOperator : IsCompactOperator (centeredOperator A μ) :=
  (isCompactOperator_Tcont A μ).clm_comp (ContinuousMap.toLp 2 μ ℝ : C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 μ)

theorem isCompactOperator_centeredOperatorC : IsCompactOperator (centeredOperatorC A μ) :=
  (isCompactOperator_Tcont A μ).comp_clm (ContinuousMap.toLp 2 μ ℝ : C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 μ)

theorem centeredOperator_apply_ae (f : Lp ℝ 2 μ) :
    centeredOperator A μ f =ᵐ[μ] fun x => ∫ y, centeredKernel A μ x y * f y ∂μ := by
  unfold centeredOperator
  have := ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ) (Tcont A μ f)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  filter_upwards [this] with x hx
  rw [hx]; exact Tcont_apply A μ f x

omit [IsProbabilityMeasure μ] in
theorem inner_eq_integral (f g : Lp ℝ 2 μ) : ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem integrable_lp (f : Lp ℝ 2 μ) : Integrable f μ :=
  (Lp.memLp f).integrable (by norm_num)

theorem centeredOperator_selfAdjoint (f g : Lp ℝ 2 μ) :
    ⟪centeredOperator A μ f, g⟫ = ⟪f, centeredOperator A μ g⟫ := by
  have hK : Continuous fun p : Torus d × Torus d => centeredKernel A μ p.1 p.2 :=
    centeredKernel_continuous A μ
  have hfg : Integrable (fun p : Torus d × Torus d => g p.1 * f p.2) (μ.prod μ) :=
    (integrable_lp μ g).mul_prod (integrable_lp μ f)
  have hint : Integrable (fun p : Torus d × Torus d =>
      centeredKernel A μ p.1 p.2 * (g p.1 * f p.2)) (μ.prod μ) :=
    hfg.bdd_mul hK.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using abs_centeredKernel_le A μ p.1 p.2)
  have e1 : ⟪centeredOperator A μ f, g⟫ =
      ∫ x, ∫ y, centeredKernel A μ x y * (g x * f y) ∂μ ∂μ := by
    rw [inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [centeredOperator_apply_ae A μ f] with x hx
    rw [hx, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have e2 : ⟪f, centeredOperator A μ g⟫ =
      ∫ y, ∫ x, centeredKernel A μ x y * (g x * f y) ∂μ ∂μ := by
    rw [inner_eq_integral]
    have : ∀ᵐ y ∂μ, f y * centeredOperator A μ g y =
        ∫ x, centeredKernel A μ x y * (g x * f y) ∂μ := by
      filter_upwards [centeredOperator_apply_ae A μ g] with y hy
      rw [hy, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [centeredKernel_symm A μ y x]; ring
    exact integral_congr_ae this
  rw [e1, e2]
  exact integral_integral_swap (f := fun x y => centeredKernel A μ x y * (g x * f y)) hint

/-- the constant function `1` in `L²(μ)`. -/
noncomputable def oneL : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ (ContinuousMap.const (Torus d) (1 : ℝ))

theorem oneL_ae : oneL μ =ᵐ[μ] fun _ => (1 : ℝ) := by
  unfold oneL
  have := ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ) (ContinuousMap.const (Torus d) (1 : ℝ))
  filter_upwards [this] with x hx
  rw [hx]; rfl

theorem inner_oneL (f : Lp ℝ 2 μ) : ⟪oneL μ, f⟫ = ∫ y, f y ∂μ := by
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [oneL_ae μ] with y hy
  rw [hy, one_mul]

theorem centeredOperator_oneL : centeredOperator A μ (oneL μ) = 0 := by
  have h : centeredOperator A μ (oneL μ) =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [centeredOperator_apply_ae A μ (oneL μ)] with x hx
    rw [hx]
    have : ∫ y, centeredKernel A μ x y * oneL μ y ∂μ = ∫ y, centeredKernel A μ x y ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [oneL_ae μ] with y hy
      rw [hy, mul_one]
    rw [this, integral_centeredKernel_right]
  exact Lp.ext (h.trans (Lp.coeFn_zero _ _ _).symm)

theorem integral_centeredOperator (f : Lp ℝ 2 μ) : ∫ x, centeredOperator A μ f x ∂μ = 0 := by
  rw [← inner_oneL, ← centeredOperator_selfAdjoint, centeredOperator_oneL]
  simp

end Kernel

section Perturb

/-- the measure `u · μ`. -/
noncomputable def perturb (μ : Measure (Torus d)) (u : Torus d → ℝ) : Measure (Torus d) :=
  μ.withDensity fun x => ENNReal.ofReal (u x)

theorem integral_perturb {μ : Measure (Torus d)} {u : Torus d → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, 0 ≤ u x) (g : Torus d → ℝ) :
    ∫ x, g x ∂(perturb μ u) = ∫ x, u x * g x ∂μ := by
  unfold perturb
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hu0 x)]

theorem isProbabilityMeasure_perturb {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {u : Torus d → ℝ} (hu : Continuous u) (hu0 : ∀ x, 0 ≤ u x) (h1 : ∫ x, u x ∂μ = 1) :
    IsProbabilityMeasure (perturb μ u) := by
  constructor
  unfold perturb
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_of_continuous_torus hu μ)
      (Filter.Eventually.of_forall hu0), h1]
  simp

theorem klDiv_perturb {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {u : Torus d → ℝ}
    (hu : Continuous u) (hu0 : ∀ x, 0 < u x) (h1 : ∫ x, u x ∂μ = 1) :
    InformationTheory.klDiv (perturb μ u) μ ≠ ⊤ ∧
      (InformationTheory.klDiv (perturb μ u) μ).toReal = ∫ x, u x * Real.log (u x) ∂μ := by
  have := isProbabilityMeasure_perturb (μ := μ) hu (fun x => (hu0 x).le) h1
  have hac : perturb μ u ≪ μ := withDensity_absolutelyContinuous _ _
  have hrn : (perturb μ u).rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (u x) :=
    Measure.rnDeriv_withDensity μ (by fun_prop)
  have hllr : llr (perturb μ u) μ =ᵐ[μ] fun x => Real.log (u x) := by
    filter_upwards [hrn] with x hx
    simp only [llr_def, hx, ENNReal.toReal_ofReal (hu0 x).le]
  have hlogc : Continuous fun x => Real.log (u x) := hu.log (fun x => (hu0 x).ne')
  have hint : Integrable (llr (perturb μ u) μ) (perturb μ u) :=
    (integrable_of_continuous_torus hlogc (perturb μ u)).congr (hac.ae_eq hllr.symm)
  refine ⟨InformationTheory.klDiv_ne_top hac hint, ?_⟩
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by rw [measure_univ, measure_univ])]
  rw [integral_congr_ae (hac.ae_eq hllr), integral_perturb hu (fun x => (hu0 x).le)]

end Perturb

section Variation

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem entropy_quadratic_nonneg
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (ν : ProbabilityMeasure (Torus d))
    (hν : InformationTheory.klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤) :
    0 ≤ (InformationTheory.klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
      (1 / 2 : ℝ) * ∫ p, centeredKernel A (μ : Measure (Torus d)) p.1 p.2
        ∂((ν : Measure (Torus d)).prod (ν : Measure (Torus d))) := by
  have hμ := minimizer_eq_gibbs A μ hmin
  have hνh : InformationTheory.klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [← klDiv_gibbs_ne_top_iff A (μ : Measure (Torus d)) (ν : Measure (Torus d)), ← hμ]
    exact hν
  have hμh : InformationTheory.klDiv (μ : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [← klDiv_gibbs_ne_top_iff A (μ : Measure (Torus d)) (μ : Measure (Torus d)), ← hμ]
    simp
  have hsub := free_energy_sub_eq A μ hμ ν (by rwa [Analysis.relativeEntropy_eq_klDiv])
  have hle := hmin ν
  rw [freeEnergy_eq_coe A ν hνh, freeEnergy_eq_coe A μ hμh, ← EReal.coe_sub,
    Analysis.relativeEntropy_eq_klDiv, ← EReal.coe_ennreal_toReal hν, ← EReal.coe_add,
    EReal.coe_eq_coe_iff] at hsub
  rw [freeEnergy_eq_coe A ν hνh, freeEnergy_eq_coe A μ hμh, EReal.coe_le_coe_iff] at hle
  linarith

end Variation

section Quadratic

variable (A : InteractionData d) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- `(T h)(x) = ∫ K(x,y) h(y) dμ(y)` for a function `h`. -/
noncomputable def Tfun (h : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, centeredKernel A μ x y * h y ∂μ

theorem exists_abs_bound {h : Torus d → ℝ} (hh : Continuous h) : ∃ B : ℝ, 0 < B ∧ ∀ x, |h x| ≤ B := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hh.continuousOn
  refine ⟨|M| + 1, by positivity, fun x => ?_⟩
  have := hM x trivial
  rw [Real.norm_eq_abs] at this
  exact this.trans (by linarith [le_abs_self M])

theorem integrable_kernel_mul {h : Torus d → ℝ} (hh : Continuous h) :
    Integrable (fun p : Torus d × Torus d => centeredKernel A μ p.1 p.2 * h p.2) (μ.prod μ) :=
  (((centeredKernel_continuous A μ).mul (hh.comp continuous_snd))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_Tfun {h : Torus d → ℝ} (hh : Continuous h) : Integrable (Tfun A μ h) μ :=
  (integrable_kernel_mul A μ hh).integral_prod_left

theorem integral_Tfun {h : Torus d → ℝ} (hh : Continuous h) : ∫ x, Tfun A μ h x ∂μ = 0 := by
  unfold Tfun
  rw [integral_integral_swap (f := fun x y => centeredKernel A μ x y * h y)
    (integrable_kernel_mul A μ hh)]
  refine (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_))
  show ∫ x, centeredKernel A μ x y * h y ∂μ = 0
  rw [integral_mul_const]
  have : ∫ x, centeredKernel A μ x y ∂μ = 0 := by
    simp_rw [centeredKernel_symm A μ _ y]
    exact integral_centeredKernel_right A μ y
  rw [this, zero_mul]

theorem inner_perturb {h : Torus d → ℝ} (hh : Continuous h) (t : ℝ) (x : Torus d) :
    ∫ y, (1 + t * h y) * centeredKernel A μ x y ∂μ = t * Tfun A μ h x := by
  have hK : Continuous fun y => centeredKernel A μ x y :=
    (centeredKernel_continuous A μ).comp (continuous_const.prodMk continuous_id)
  have i1 : Integrable (fun y => centeredKernel A μ x y) μ := integrable_of_continuous_torus hK μ
  have i2 : Integrable (fun y => centeredKernel A μ x y * h y) μ :=
    integrable_of_continuous_torus (hK.mul hh) μ
  have : ∀ y, (1 + t * h y) * centeredKernel A μ x y =
      centeredKernel A μ x y + t * (centeredKernel A μ x y * h y) := fun y => by ring
  simp_rw [this]
  rw [integral_add i1 (i2.const_mul t), integral_const_mul, integral_centeredKernel_right]
  simp [Tfun]

theorem integral_kernel_perturb {h : Torus d → ℝ} (hh : Continuous h) (hm : ∫ x, h x ∂μ = 0)
    (t : ℝ) (ht : ∀ x, 0 ≤ 1 + t * h x) :
    ∫ p, centeredKernel A μ p.1 p.2
      ∂((perturb μ (fun x => 1 + t * h x)).prod (perturb μ (fun x => 1 + t * h x))) =
      t ^ 2 * ∫ x, h x * Tfun A μ h x ∂μ := by
  have hu : Continuous fun x => 1 + t * h x := continuous_const.add (continuous_const.mul hh)
  have h1 : ∫ x, (1 + t * h x) ∂μ = 1 := by
    rw [integral_add (integrable_const _) ((integrable_of_continuous_torus hh μ).const_mul t),
      integral_const_mul, hm]
    simp
  have := isProbabilityMeasure_perturb (μ := μ) hu ht h1
  have hint : Integrable (fun p : Torus d × Torus d => centeredKernel A μ p.1 p.2)
      ((perturb μ (fun x => 1 + t * h x)).prod (perturb μ (fun x => 1 + t * h x))) :=
    (centeredKernel_continuous A μ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_prod _ hint]
  have e1 : ∀ x, ∫ y, centeredKernel A μ x y ∂(perturb μ (fun x => 1 + t * h x)) =
      t * Tfun A μ h x := fun x => by
    rw [integral_perturb hu ht]; exact inner_perturb A μ hh t x
  simp_rw [e1]
  rw [integral_perturb hu ht (fun x => t * Tfun A μ h x)]
  obtain ⟨B, hB0, hB⟩ := exists_abs_bound hh
  have hT := integrable_Tfun A μ hh
  have hhT : Integrable (fun x => h x * Tfun A μ h x) μ :=
    hT.bdd_mul hh.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hB x)
  have : ∀ x, (1 + t * h x) * (t * Tfun A μ h x) =
      t * Tfun A μ h x + t ^ 2 * (h x * Tfun A μ h x) := fun x => by ring
  simp_rw [this]
  rw [integral_add (hT.const_mul t) (hhT.const_mul _), integral_const_mul, integral_const_mul,
    integral_Tfun A μ hh]
  simp

end Quadratic

theorem entropy_scalar_bound {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(1 + s) * Real.log (1 + s) - s - s ^ 2 / 2| ≤ 4 * |s| ^ 3 := by
  have h1 : |(-s)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hab : 0 ≤ |s| := abs_nonneg s
  have hd : |s| ^ 3 / (1 - |s|) ≤ 2 * |s| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg hab 3]
  have h2 : |(-s + s ^ 2 / 2 + Real.log (1 + s))| ≤ 2 * |s| ^ 3 := h.trans hd
  set r := -s + s ^ 2 / 2 + Real.log (1 + s) with hr
  have e : (1 + s) * Real.log (1 + s) - s - s ^ 2 / 2 = (1 + s) * r - s ^ 3 / 2 := by
    rw [hr]; ring
  rw [e]
  have h3 : |1 + s| ≤ 3 / 2 := by rw [abs_le]; constructor <;> linarith [abs_le.mp hs]
  have h4 : |(1 + s) * r| ≤ 3 * |s| ^ 3 := by
    rw [abs_mul]
    calc |1 + s| * |r| ≤ (3 / 2) * (2 * |s| ^ 3) :=
          mul_le_mul h3 h2 (abs_nonneg _) (by norm_num)
      _ = 3 * |s| ^ 3 := by ring
  have h5 : |s ^ 3 / 2| = |s| ^ 3 / 2 := by rw [abs_div, abs_pow]; norm_num
  calc |(1 + s) * r - s ^ 3 / 2| ≤ |(1 + s) * r| + |s ^ 3 / 2| := abs_sub _ _
    _ ≤ 4 * |s| ^ 3 := by rw [h5]; nlinarith [pow_nonneg hab 3]

section Hessian

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem hessian_nonneg_continuous
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    {h : Torus d → ℝ} (hh : Continuous h) (hm : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    0 ≤ ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) +
      ∫ x, h x * Tfun A (μ : Measure (Torus d)) h x ∂(μ : Measure (Torus d)) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_bound hh
  set I2 := ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) with hI2
  set Q := ∫ x, h x * Tfun A (μ : Measure (Torus d)) h x ∂(μ : Measure (Torus d)) with hQ
  have hI2nn : 0 ≤ I2 := integral_nonneg fun x => sq_nonneg _
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * B) → 0 ≤ (I2 + Q) / 2 + 4 * t * B * I2 := by
    intro t ht0 htB
    have hts : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
      rw [abs_mul, abs_of_pos ht0]
      calc t * |h x| ≤ t * B := mul_le_mul_of_nonneg_left (hB x) ht0.le
        _ ≤ 1 / (2 * B) * B := mul_le_mul_of_nonneg_right htB hB0.le
        _ = 1 / 2 := by field_simp
    have hu0 : ∀ x, 0 < 1 + t * h x := fun x => by
      have := abs_le.mp (hts x); linarith
    have hu : Continuous fun x => 1 + t * h x := continuous_const.add (continuous_const.mul hh)
    have h1 : ∫ x, (1 + t * h x) ∂(μ : Measure (Torus d)) = 1 := by
      rw [integral_add (integrable_const _)
        ((integrable_of_continuous_torus hh _).const_mul t), integral_const_mul, hm]
      simp
    have hprob := isProbabilityMeasure_perturb (μ := (μ : Measure (Torus d))) hu
      (fun x => (hu0 x).le) h1
    obtain ⟨hne, hval⟩ := klDiv_perturb (μ := (μ : Measure (Torus d))) hu hu0 h1
    have hnn := entropy_quadratic_nonneg A μ hmin ⟨perturb (μ : Measure (Torus d))
      (fun x => 1 + t * h x), hprob⟩ hne
    simp only [ProbabilityMeasure.coe_mk] at hnn
    rw [hval, integral_kernel_perturb A (μ : Measure (Torus d)) hh hm t (fun x => (hu0 x).le)] at hnn
    -- bound the entropy integral
    have hbound : ∫ x, (1 + t * h x) * Real.log (1 + t * h x) ∂(μ : Measure (Torus d)) ≤
        t ^ 2 / 2 * I2 + 4 * t ^ 3 * B * I2 := by
      have hc1 : Continuous fun x => (1 + t * h x) * Real.log (1 + t * h x) :=
        hu.mul (hu.log (fun x => (hu0 x).ne'))
      have hc2 : Continuous fun x => t * h x + t ^ 2 / 2 * h x ^ 2 + 4 * t ^ 3 * B * h x ^ 2 :=
        by fun_prop
      have hmono := integral_mono (integrable_of_continuous_torus hc1 (μ : Measure (Torus d)))
        (integrable_of_continuous_torus hc2 (μ : Measure (Torus d))) (fun x => by
          have hb := abs_le.mp (entropy_scalar_bound (hts x))
          have hcube : |t * h x| ^ 3 ≤ t ^ 3 * B * h x ^ 2 := by
            have e : |t * h x| ^ 3 = t ^ 3 * (|h x| * h x ^ 2) := by
              rw [abs_mul, abs_of_pos ht0, mul_pow, show |h x| ^ 3 = |h x| * |h x| ^ 2 by ring,
                sq_abs]
            rw [e, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hB x) (sq_nonneg _)) (by positivity)
          show (1 + t * h x) * Real.log (1 + t * h x) ≤
            t * h x + t ^ 2 / 2 * h x ^ 2 + 4 * t ^ 3 * B * h x ^ 2
          nlinarith [hb.2])
      refine hmono.trans (le_of_eq ?_)
      have i1 : Integrable (fun x => t * h x) (μ : Measure (Torus d)) :=
        (integrable_of_continuous_torus hh _).const_mul t
      have i2 : Integrable (fun x => h x ^ 2) (μ : Measure (Torus d)) :=
        integrable_of_continuous_torus (hh.pow 2) _
      rw [integral_add (f := fun x => t * h x + t ^ 2 / 2 * h x ^ 2)
        (g := fun x => 4 * t ^ 3 * B * h x ^ 2) (i1.add (i2.const_mul _)) (i2.const_mul _),
        integral_add (f := fun x => t * h x) (g := fun x => t ^ 2 / 2 * h x ^ 2) i1
          (i2.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hm, ← hI2]
      ring
    have h2 : 0 ≤ t ^ 2 * ((I2 + Q) / 2 + 4 * t * B * I2) := by
      nlinarith [hnn, hbound]
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h2
  by_contra hneg
  rw [not_le] at hneg
  set ε := -(I2 + Q) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set M := 4 * B * I2 with hM
  have hM0 : 0 ≤ M := by positivity
  set t := min (1 / (2 * B)) (ε / (M + 1)) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htle : t * M ≤ ε := by
    calc t * M ≤ ε / (M + 1) * M :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hM0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have := key t ht0 (min_le_left _ _)
  have e : 4 * t * B * I2 = t * M := by rw [hM]; ring
  rw [e] at this
  linarith

end Hessian

section L2Hessian

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem inner_toLp_self (g : C(Torus d, ℝ)) :
    ⟪ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g, ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g⟫ =
      ∫ x, g x ^ 2 ∂(μ : Measure (Torus d)) := by
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) g]
    with x hx
  rw [hx]; ring

theorem inner_toLp_operator (g : C(Torus d, ℝ)) :
    ⟪ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g,
      centeredOperator A (μ : Measure (Torus d)) (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g)⟫ =
      ∫ x, g x * Tfun A (μ : Measure (Torus d)) g x ∂(μ : Measure (Torus d)) := by
  have hg := ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) g
  have hTT : ∀ x, ∫ y, centeredKernel A (μ : Measure (Torus d)) x y *
      (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g) y ∂(μ : Measure (Torus d)) =
      Tfun A (μ : Measure (Torus d)) g x := fun x => by
    refine integral_congr_ae ?_
    filter_upwards [hg] with y hy
    rw [hy]
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg, centeredOperator_apply_ae A (μ : Measure (Torus d))
    (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g)] with x hx1 hx2
  rw [hx1, hx2, hTT x]

theorem hessianForm_add_const (f0 : Lp ℝ 2 (μ : Measure (Torus d)))
    (h0 : ⟪oneL (μ : Measure (Torus d)), f0⟫ = 0) (c : ℝ) :
    ⟪f0 + c • oneL (μ : Measure (Torus d)), f0 + c • oneL (μ : Measure (Torus d))⟫ +
      ⟪f0 + c • oneL (μ : Measure (Torus d)),
        centeredOperator A (μ : Measure (Torus d)) (f0 + c • oneL (μ : Measure (Torus d)))⟫ =
      (⟪f0, f0⟫ + ⟪f0, centeredOperator A (μ : Measure (Torus d)) f0⟫) + c ^ 2 := by
  have h1 : ⟪oneL (μ : Measure (Torus d)), oneL (μ : Measure (Torus d))⟫ = 1 := by
    rw [inner_oneL]
    rw [integral_congr_ae (oneL_ae (μ : Measure (Torus d)))]
    simp
  have h2 : ⟪oneL (μ : Measure (Torus d)), centeredOperator A (μ : Measure (Torus d)) f0⟫ = 0 := by
    rw [inner_oneL, integral_centeredOperator]
  have h3 : ⟪f0, oneL (μ : Measure (Torus d))⟫ = 0 := by rw [real_inner_comm]; exact h0
  rw [map_add, map_smul, centeredOperator_oneL, smul_zero, add_zero]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h3,
    RCLike.conj_to_real]
  rw [h0]
  ring

theorem hessian_nonneg
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    0 ≤ ⟪f, f⟫ + ⟪f, centeredOperator A (μ : Measure (Torus d)) f⟫ := by
  have hcont : Continuous fun f : Lp ℝ 2 (μ : Measure (Torus d)) =>
      ⟪f, f⟫ + ⟪f, centeredOperator A (μ : Measure (Torus d)) f⟫ := by
    have := (centeredOperator A (μ : Measure (Torus d))).continuous
    fun_prop
  have hclosed : IsClosed {f : Lp ℝ 2 (μ : Measure (Torus d)) |
      0 ≤ ⟪f, f⟫ + ⟪f, centeredOperator A (μ : Measure (Torus d)) f⟫} :=
    isClosed_le continuous_const hcont
  have hdense := ContinuousMap.toLp_denseRange ℝ (μ : Measure (Torus d)) ℝ (p := 2) (by simp)
  have hsub : Set.range (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ :
      C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d))) ⊆ {f : Lp ℝ 2 (μ : Measure (Torus d)) |
      0 ≤ ⟪f, f⟫ + ⟪f, centeredOperator A (μ : Measure (Torus d)) f⟫} := by
    rintro _ ⟨g, rfl⟩
    rw [Set.mem_ofPred_eq]
    set m : Measure (Torus d) := (μ : Measure (Torus d))
    set c : ℝ := ∫ x, g x ∂m with hc
    set g0 : C(Torus d, ℝ) := g - ContinuousMap.const (Torus d) c with hg0
    have hg0m : ∫ x, g0 x ∂m = 0 := by
      have : ∀ x, g0 x = g x - c := fun x => by simp [hg0]
      simp_rw [this]
      rw [integral_sub (integrable_of_continuous_torus g.continuous m) (integrable_const _)]
      simp [hc]
    have hdec : ContinuousMap.toLp 2 m ℝ g = ContinuousMap.toLp 2 m ℝ g0 + c • oneL m := by
      unfold oneL
      rw [← map_smul, ← map_add]
      congr 1
      ext x
      simp [hg0]
    have hone : ⟪oneL m, ContinuousMap.toLp 2 m ℝ g0⟫ = 0 := by
      rw [inner_oneL, ← hg0m]
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := m) (𝕜 := ℝ) g0] with x hx
      exact hx
    have hpsd := hessian_nonneg_continuous A μ hmin g0.continuous hg0m
    rw [hdec, hessianForm_add_const A μ _ hone c, inner_toLp_self, inner_toLp_operator]
    have : 0 ≤ c ^ 2 := sq_nonneg c
    linarith
  have hf : f ∈ closure (Set.range (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ :
      C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)))) := by
    rw [hdense.closure_range]; trivial
  exact closure_minimal hsub hclosed hf

end L2Hessian


section Final

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem kernel_integral_lipschitz (hA : LipschitzData A) (m : Measure (Torus d))
    [IsProbabilityMeasure m] (f : Lp ℝ 2 m) :
    ∃ L : ℝ, TorusLipschitzWith L fun x => ∫ y, centeredKernel A m x y * f y ∂m := by
  obtain ⟨LW, hLW⟩ := hA.2
  have hx : ∀ y, TorusLipschitzWith |LW| fun x => A.W x y := by
    intro y x x'
    have := hLW x y x' y
    have h0 : 0 ≤ torusDist x x' := Real.sqrt_nonneg _
    have e : Real.sqrt (torusDist x x' ^ 2 + torusDist y y ^ 2) = torusDist x x' := by
      simp [torusDist_metric.1 y, Real.sqrt_sq h0]
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0)
  have hconv := lipschitz_integral_of_lipschitz A.W_continuous hx m
  have hK : ∀ x x' y, |centeredKernel A m x y - centeredKernel A m x' y| ≤
      2 * |LW| * torusDist x x' := by
    intro x x' y
    have e : centeredKernel A m x y - centeredKernel A m x' y =
        (A.W x y - A.W x' y) - (interactionConvolution A m x - interactionConvolution A m x') := by
      unfold centeredKernel; ring
    rw [e]
    have h1 := hx y x x'
    have h2 : |interactionConvolution A m x - interactionConvolution A m x'| ≤
        |LW| * torusDist x x' := hconv x x'
    have := abs_sub (A.W x y - A.W x' y)
      (interactionConvolution A m x - interactionConvolution A m x')
    linarith
  have hint : ∀ x, Integrable (fun y => centeredKernel A m x y * f y) m := fun x => by
    have hc : Continuous fun y => centeredKernel A m x y :=
      (centeredKernel_continuous A m).comp (continuous_const.prodMk continuous_id)
    exact (integrable_lp m f).bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using abs_centeredKernel_le A m x y)
  refine ⟨2 * |LW| * ∫ y, |f y| ∂m, fun x x' => ?_⟩
  rw [← integral_sub (hint x) (hint x')]
  have hfi : Integrable (fun y => |f y|) m := (integrable_lp m f).abs
  have h0 : 0 ≤ torusDist x x' := Real.sqrt_nonneg _
  calc |∫ y, (centeredKernel A m x y * f y - centeredKernel A m x' y * f y) ∂m|
      ≤ ∫ y, |centeredKernel A m x y * f y - centeredKernel A m x' y * f y| ∂m := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := m)
            (fun y => centeredKernel A m x y * f y - centeredKernel A m x' y * f y)
    _ ≤ ∫ y, 2 * |LW| * torusDist x x' * |f y| ∂m := by
        refine integral_mono ((((hint x).sub (hint x')).abs)) (hfi.const_mul _) fun y => ?_
        have : centeredKernel A m x y * f y - centeredKernel A m x' y * f y =
            (centeredKernel A m x y - centeredKernel A m x' y) * f y := by ring
        simp only
        rw [this, abs_mul]
        exact mul_le_mul_of_nonneg_right (hK x x' y) (abs_nonneg _)
    _ = 2 * |LW| * (∫ y, |f y| ∂m) * torusDist x x' := by
        rw [integral_const_mul]; ring

/-- the mean-zero subspace of `L²(μ)`. -/
noncomputable def meanZeroL2 : Submodule ℝ (Lp ℝ 2 (μ : Measure (Torus d))) :=
  LinearMap.ker ((innerSL ℝ (oneL (μ : Measure (Torus d))) :
    Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] ℝ) : Lp ℝ 2 (μ : Measure (Torus d)) →ₗ[ℝ] ℝ)

theorem mem_meanZeroL2 (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    f ∈ meanZeroL2 μ ↔ ∫ x, f x ∂(μ : Measure (Torus d)) = 0 := by
  unfold meanZeroL2
  rw [LinearMap.mem_ker]
  show ⟪oneL (μ : Measure (Torus d)), f⟫ = 0 ↔ _
  rw [inner_oneL]

theorem isClosed_meanZeroL2 : IsClosed (meanZeroL2 μ : Set (Lp ℝ 2 (μ : Measure (Torus d)))) :=
  ContinuousLinearMap.isClosed_ker (innerSL ℝ (oneL (μ : Measure (Torus d))))

instance : CompleteSpace (meanZeroL2 μ) := (isClosed_meanZeroL2 μ).completeSpace_coe

/-- the centered kernel operator on `L²(μ)` restricted to the mean-zero subspace. -/
noncomputable def centeredOperatorSub : meanZeroL2 μ →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)) :=
  (centeredOperator A (μ : Measure (Torus d))).comp (meanZeroL2 μ).subtypeL

theorem centeredOperatorSub_apply (f : meanZeroL2 μ) :
    centeredOperatorSub A μ f = centeredOperator A (μ : Measure (Torus d)) (f : Lp ℝ 2 (μ : Measure (Torus d))) :=
  rfl

theorem centeredOperatorSub_mem (f : meanZeroL2 μ) : centeredOperatorSub A μ f ∈ meanZeroL2 μ := by
  rw [mem_meanZeroL2, centeredOperatorSub_apply]
  exact integral_centeredOperator A _ _

/-- the centered kernel operator on the mean-zero subspace. -/
noncomputable def centeredOperator0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ :=
  (centeredOperatorSub A μ).codRestrict (meanZeroL2 μ) (centeredOperatorSub_mem A μ)

theorem coe_centeredOperator0 (f : meanZeroL2 μ) :
    ((centeredOperator0 A μ f : meanZeroL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) =
      centeredOperator A (μ : Measure (Torus d)) f := rfl

theorem isCompactOperator_centeredOperator0 : IsCompactOperator (centeredOperator0 A μ) :=
  ((isCompactOperator_centeredOperator A (μ : Measure (Torus d))).comp_clm
    (meanZeroL2 μ).subtypeL).codRestrict (centeredOperatorSub_mem A μ) (isClosed_meanZeroL2 μ)

theorem centeredOperator0_symm (f g : meanZeroL2 μ) :
    ⟪centeredOperator0 A μ f, g⟫ = ⟪f, centeredOperator0 A μ g⟫ :=
  centeredOperator_selfAdjoint A (μ : Measure (Torus d)) f g

theorem isSelfAdjoint_centeredOperator0 : IsSelfAdjoint (centeredOperator0 A μ) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (centeredOperator0_symm A μ)

theorem centeredOperator0_psd
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (f : meanZeroL2 μ) : 0 ≤ ⟪f + centeredOperator0 A μ f, f⟫ := by
  have := hessian_nonneg A μ hmin f
  rw [real_inner_comm (centeredOperator A (μ : Measure (Torus d)) f)
    (f : Lp ℝ 2 (μ : Measure (Torus d)))] at this
  rw [inner_add_left]
  exact this


/-- the null space `E = ker (I + T)` inside the mean-zero subspace. -/
noncomputable def nullspace : Submodule ℝ (meanZeroL2 μ) :=
  LinearMap.ker ((ContinuousLinearMap.id ℝ (meanZeroL2 μ) + centeredOperator0 A μ :
    meanZeroL2 μ →L[ℝ] meanZeroL2 μ) : meanZeroL2 μ →ₗ[ℝ] meanZeroL2 μ)

theorem mem_nullspace (f : meanZeroL2 μ) :
    f ∈ nullspace A μ ↔ f + centeredOperator0 A μ f = 0 := by
  unfold nullspace
  rw [LinearMap.mem_ker]
  rfl

theorem isClosed_nullspace : IsClosed (nullspace A μ : Set (meanZeroL2 μ)) :=
  ContinuousLinearMap.isClosed_ker
    (ContinuousLinearMap.id ℝ (meanZeroL2 μ) + centeredOperator0 A μ)

instance : CompleteSpace (nullspace A μ) := (isClosed_nullspace A μ).completeSpace_coe

theorem centeredOperator0_of_mem {f : meanZeroL2 μ} (hf : f ∈ nullspace A μ) :
    centeredOperator0 A μ f = -f :=
  eq_neg_of_add_eq_zero_right ((mem_nullspace A μ f).1 hf)

theorem finiteDimensional_nullspace : FiniteDimensional ℝ (nullspace A μ) := by
  let N : meanZeroL2 μ →ₗ[ℝ] meanZeroL2 μ := -(centeredOperator0 A μ : meanZeroL2 μ →ₗ[ℝ] meanZeroL2 μ)
  have hN : IsCompactOperator N := (isCompactOperator_centeredOperator0 A μ).neg
  have hV : ∀ v ∈ nullspace A μ, N v ∈ nullspace A μ := fun v hv => by
    have : N v = v := by
      show -(centeredOperator0 A μ v) = v
      rw [centeredOperator0_of_mem A μ hv, neg_neg]
    rw [this]; exact hv
  have h := hN.restrict hV (isClosed_nullspace A μ)
  have e : (N.restrict hV : nullspace A μ → nullspace A μ) = id := by
    funext v
    apply Subtype.ext
    show N v = v
    show -(centeredOperator0 A μ v) = v
    rw [centeredOperator0_of_mem A μ v.2, neg_neg]
  rw [e] at h
  exact FiniteDimensional.of_isCompactOperator_id h

theorem lipschitz_representative_of_eigen (hA : LipschitzData A) (m : Measure (Torus d))
    [IsProbabilityMeasure m] (F : Lp ℝ 2 m) (hF : centeredOperator A m F = -F) :
    ∃ (L : ℝ) (g : Torus d → ℝ), TorusLipschitzWith L g ∧ F =ᵐ[m] g := by
  obtain ⟨L, hL⟩ := kernel_integral_lipschitz A hA m F
  refine ⟨L, fun x => -∫ y, centeredKernel A m x y * F y ∂m, fun x x' => ?_, ?_⟩
  · have := hL x x'
    rw [show (-∫ y, centeredKernel A m x y * F y ∂m) - (-∫ y, centeredKernel A m x' y * F y ∂m) =
      -((∫ y, centeredKernel A m x y * F y ∂m) - ∫ y, centeredKernel A m x' y * F y ∂m) by ring,
      abs_neg]
    exact this
  · filter_upwards [centeredOperator_apply_ae A m F, Lp.coeFn_neg F] with x hx hn
    rw [hF, hn] at hx
    simp only [Pi.neg_apply] at hx
    linarith

theorem nullspace_lipschitz_representative (hA : LipschitzData A) (f : meanZeroL2 μ)
    (hf : f ∈ nullspace A μ) :
    ∃ (L : ℝ) (g : Torus d → ℝ), TorusLipschitzWith L g ∧
      (f : Lp ℝ 2 (μ : Measure (Torus d))) =ᵐ[(μ : Measure (Torus d))] g :=
  lipschitz_representative_of_eigen A hA (μ : Measure (Torus d)) _ (by
    have h1 : (centeredOperator0 A μ f : Lp ℝ 2 (μ : Measure (Torus d))) =
        -(f : Lp ℝ 2 (μ : Measure (Torus d))) := by
      rw [centeredOperator0_of_mem A μ hf]; rfl
    exact h1)


theorem centeredOperator_of_mem_nullspace {f : meanZeroL2 μ} (hf : f ∈ nullspace A μ) :
    centeredOperator A (μ : Measure (Torus d)) (f : Lp ℝ 2 (μ : Measure (Torus d))) =
      -(f : Lp ℝ 2 (μ : Measure (Torus d))) := by
  have h1 : (centeredOperator0 A μ f : Lp ℝ 2 (μ : Measure (Torus d))) =
      -(f : Lp ℝ 2 (μ : Measure (Torus d))) := by
    rw [centeredOperator0_of_mem A μ hf]; rfl
  exact h1

/-- the continuous mean-zero functions orthogonal to the null space `E`. -/
noncomputable def Ysub : Submodule ℝ C(Torus d, ℝ) :=
  (meanZeroL2 μ ⊓ ((nullspace A μ).map (meanZeroL2 μ).subtype)ᗮ).comap
    ((ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ :
      C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d))) :
      C(Torus d, ℝ) →ₗ[ℝ] Lp ℝ 2 (μ : Measure (Torus d)))

theorem integral_toLp_eq (u : C(Torus d, ℝ)) :
    ∫ x, (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ u) x ∂(μ : Measure (Torus d)) =
      ∫ x, u x ∂(μ : Measure (Torus d)) := by
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) u]
    with x hx
  exact hx

theorem mem_Ysub (u : C(Torus d, ℝ)) :
    u ∈ Ysub A μ ↔ (∫ x, u x ∂(μ : Measure (Torus d)) = 0) ∧
      ∀ e ∈ nullspace A μ, ⟪((e : meanZeroL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))),
        ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ u⟫ = 0 := by
  unfold Ysub
  rw [Submodule.mem_comap, Submodule.mem_inf, mem_meanZeroL2, Submodule.mem_orthogonal]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun e he => h2 _ ⟨e, he, rfl⟩⟩
    exact (integral_toLp_eq μ u).symm.trans h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact (integral_toLp_eq μ u).trans h1
    · rintro _ ⟨e, he, rfl⟩
      exact h2 e he

theorem isClosed_Ysub : IsClosed (Ysub A μ : Set C(Torus d, ℝ)) := by
  have hc : Continuous (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ :
      C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d))) :=
    ContinuousLinearMap.continuous _
  have h : IsClosed ((meanZeroL2 μ ⊓ ((nullspace A μ).map (meanZeroL2 μ).subtype)ᗮ :
      Submodule ℝ (Lp ℝ 2 (μ : Measure (Torus d)))) : Set (Lp ℝ 2 (μ : Measure (Torus d)))) := by
    rw [Submodule.coe_inf]
    exact (isClosed_meanZeroL2 μ).inter (Submodule.isClosed_orthogonal _)
  exact h.preimage hc

instance : CompleteSpace (Ysub A μ) := (isClosed_Ysub A μ).completeSpace_coe

theorem toLp_centeredOperatorC (u : C(Torus d, ℝ)) :
    ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ (centeredOperatorC A (μ : Measure (Torus d)) u) =
      centeredOperator A (μ : Measure (Torus d))
        (ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ u) := rfl

theorem centeredOperatorC_mem {u : C(Torus d, ℝ)} (hu : u ∈ Ysub A μ) :
    centeredOperatorC A (μ : Measure (Torus d)) u ∈ Ysub A μ := by
  rw [mem_Ysub] at hu ⊢
  obtain ⟨_, h2⟩ := hu
  refine ⟨?_, fun e he => ?_⟩
  · rw [← integral_toLp_eq, toLp_centeredOperatorC]
    exact integral_centeredOperator A _ _
  · rw [toLp_centeredOperatorC, ← centeredOperator_selfAdjoint, centeredOperator_of_mem_nullspace A μ he,
      inner_neg_left, h2 e he, neg_zero]

/-- the centered kernel operator on `C(𝕋)`, restricted to `Y`, as a map into `C(𝕋)`. -/
noncomputable def centeredOperatorCsub : Ysub A μ →L[ℝ] C(Torus d, ℝ) :=
  (centeredOperatorC A (μ : Measure (Torus d))).comp (Ysub A μ).subtypeL

theorem centeredOperatorCsub_apply (u : Ysub A μ) :
    centeredOperatorCsub A μ u = centeredOperatorC A (μ : Measure (Torus d)) (u : C(Torus d, ℝ)) :=
  rfl

theorem centeredOperatorCsub_mem (u : Ysub A μ) : centeredOperatorCsub A μ u ∈ Ysub A μ := by
  rw [centeredOperatorCsub_apply]
  exact centeredOperatorC_mem A μ u.2

/-- the centered kernel operator on `Y`. -/
noncomputable def centeredOperatorY : Ysub A μ →L[ℝ] Ysub A μ :=
  (centeredOperatorCsub A μ).codRestrict (Ysub A μ) (centeredOperatorCsub_mem A μ)

theorem coe_centeredOperatorY (u : Ysub A μ) :
    ((centeredOperatorY A μ u : Ysub A μ) : C(Torus d, ℝ)) =
      centeredOperatorC A (μ : Measure (Torus d)) (u : C(Torus d, ℝ)) := rfl

theorem isCompactOperator_centeredOperatorY : IsCompactOperator (centeredOperatorY A μ) :=
  ((isCompactOperator_centeredOperatorC A (μ : Measure (Torus d))).comp_clm
    (Ysub A μ).subtypeL).codRestrict (centeredOperatorCsub_mem A μ) (isClosed_Ysub A μ)

theorem injective_on_Ysub (v : Ysub A μ)
    (hv : (v : C(Torus d, ℝ)) + centeredOperatorC A (μ : Measure (Torus d)) (v : C(Torus d, ℝ)) = 0) :
    v = 0 := by
  have hv' := (mem_Ysub A μ _).1 v.2
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  set F : Lp ℝ 2 m := ContinuousMap.toLp 2 m ℝ (v : C(Torus d, ℝ)) with hF
  have hmean : F ∈ meanZeroL2 μ := (mem_meanZeroL2 μ F).2 (by rw [hF, integral_toLp_eq]; exact hv'.1)
  have hTF : centeredOperator A m F = -F := by
    have h1 : centeredOperatorC A m (v : C(Torus d, ℝ)) = -(v : C(Torus d, ℝ)) :=
      eq_neg_of_add_eq_zero_right hv
    have := toLp_centeredOperatorC A μ (v : C(Torus d, ℝ))
    rw [h1, map_neg] at this
    exact this.symm
  have hE : (⟨F, hmean⟩ : meanZeroL2 μ) ∈ nullspace A μ := by
    rw [mem_nullspace]
    apply Subtype.ext
    show F + centeredOperator A m F = 0
    rw [hTF]; simp
  have h0 := hv'.2 _ hE
  have hF0 : F = 0 := by
    have : ⟪F, F⟫ = 0 := h0
    exact inner_self_eq_zero.1 this
  have : centeredOperatorC A m (v : C(Torus d, ℝ)) = 0 := by
    show Tcont A m (ContinuousMap.toLp 2 m ℝ (v : C(Torus d, ℝ))) = 0
    rw [← hF, hF0, map_zero]
  have hvz : (v : C(Torus d, ℝ)) = 0 := by
    rw [this, add_zero] at hv; exact hv
  exact Subtype.ext hvz

theorem fredholm_inverse_Ysub :
    ∃ S : Ysub A μ →L[ℝ] Ysub A μ, ∀ y z : Ysub A μ,
      ((z : C(Torus d, ℝ)) + centeredOperatorC A (μ : Measure (Torus d)) (z : C(Torus d, ℝ)) =
        (y : C(Torus d, ℝ))) ↔ S y = z := by
  have hT := isCompactOperator_centeredOperatorY A μ
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (𝕜 := ℝ) (X := Ysub A μ)
    (T := centeredOperatorY A μ) hT (μ := (-1 : ℝ)) (by norm_num) with h | h
  · exfalso
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have h1 := hv.apply_eq_smul
    have h2 : centeredOperatorY A μ v = -v := by
      simpa using h1
    have h3 : (v : C(Torus d, ℝ)) + centeredOperatorC A (μ : Measure (Torus d)) (v : C(Torus d, ℝ)) = 0 := by
      have := congrArg (fun w : Ysub A μ => (w : C(Torus d, ℝ))) h2
      simp only [coe_centeredOperatorY] at this
      simp [this]
    exact hv.2 (injective_on_Ysub A μ v h3)
  · rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, neg_one_smul] at h
    have hB : IsUnit (1 + centeredOperatorY A μ : Ysub A μ →L[ℝ] Ysub A μ) := by
      have e : (1 + centeredOperatorY A μ : Ysub A μ →L[ℝ] Ysub A μ) =
          -((-1 : Ysub A μ →L[ℝ] Ysub A μ) - centeredOperatorY A μ) := by abel
      rw [e]; exact h.neg
    obtain ⟨u, hu⟩ := hB
    obtain ⟨S, hS⟩ : ∃ S : Ysub A μ →L[ℝ] Ysub A μ, S = ((u⁻¹ : (Ysub A μ →L[ℝ] Ysub A μ)ˣ) :
        Ysub A μ →L[ℝ] Ysub A μ) := ⟨_, rfl⟩
    have hSu : S * (1 + centeredOperatorY A μ) = 1 := by rw [← hu, hS]; exact u.inv_mul
    have huS : (1 + centeredOperatorY A μ) * S = 1 := by rw [← hu, hS]; exact u.mul_inv
    refine ⟨S, fun y z => ?_⟩
    have key : ∀ w : Ysub A μ, (((1 + centeredOperatorY A μ : Ysub A μ →L[ℝ] Ysub A μ) w : Ysub A μ) :
        C(Torus d, ℝ)) = (w : C(Torus d, ℝ)) +
          centeredOperatorC A (μ : Measure (Torus d)) (w : C(Torus d, ℝ)) := fun w => rfl
    constructor
    · intro hz
      have h1 : (1 + centeredOperatorY A μ : Ysub A μ →L[ℝ] Ysub A μ) z = y :=
        Subtype.ext (by rw [key]; exact hz)
      have h2 := congrArg (fun w : Ysub A μ →L[ℝ] Ysub A μ => w z) hSu
      rw [← h1]
      exact h2
    · intro hz
      have h2 := congrArg (fun w : Ysub A μ →L[ℝ] Ysub A μ => w y) huS
      have h3 : (1 + centeredOperatorY A μ : Ysub A μ →L[ℝ] Ysub A μ) z = y := by
        rw [← hz]; exact h2
      rw [← h3, key]

/-- **LIP033.** At a minimizer `μ`, the centered kernel operator `T` on the mean-zero subspace
`L²₀(μ)` is compact and self-adjoint with `I + T ≥ 0`; `E = ker (I + T)` is finite-dimensional;
every element of `E` has a Lipschitz representative (under `LipschitzData`, from `h = -T h`); and on
the continuous mean-zero functions `Y` orthogonal to `E`, `T` preserves `Y` and `I + T : Y → Y` has a
bounded inverse. -/
theorem centered_hessian_positive_semidefinite_and_finite_nullspace
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    IsCompactOperator (centeredOperator0 A μ) ∧ IsSelfAdjoint (centeredOperator0 A μ) ∧
    (∀ f : meanZeroL2 μ, 0 ≤ ⟪f + centeredOperator0 A μ f, f⟫) ∧
    FiniteDimensional ℝ (nullspace A μ) ∧
    (LipschitzData A → ∀ f ∈ nullspace A μ, ∃ (L : ℝ) (g : Torus d → ℝ),
      TorusLipschitzWith L g ∧
        (f : Lp ℝ 2 (μ : Measure (Torus d))) =ᵐ[(μ : Measure (Torus d))] g) ∧
    (∀ u ∈ Ysub A μ, centeredOperatorC A (μ : Measure (Torus d)) u ∈ Ysub A μ) ∧
    ∃ S : Ysub A μ →L[ℝ] Ysub A μ, ∀ y z : Ysub A μ,
      ((z : C(Torus d, ℝ)) + centeredOperatorC A (μ : Measure (Torus d)) (z : C(Torus d, ℝ)) =
        (y : C(Torus d, ℝ))) ↔ S y = z :=
  ⟨isCompactOperator_centeredOperator0 A μ, isSelfAdjoint_centeredOperator0 A μ,
    centeredOperator0_psd A μ hmin, finiteDimensional_nullspace A μ,
    fun hA f hf => nullspace_lipschitz_representative A μ hA f hf,
    fun _ hu => centeredOperatorC_mem A μ hu, fredholm_inverse_Ysub A μ⟩

end Final

end DGPS.Lipschitz
