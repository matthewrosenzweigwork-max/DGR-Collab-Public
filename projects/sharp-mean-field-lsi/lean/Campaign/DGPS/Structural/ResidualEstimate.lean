import DGPS.Structural.FrozenGibbsDerivative

/-!
# Coercive density Hessian gives a local residual estimate (STR006)

If `μ = Pμ` and the density Hessian is coercive, then `I - DPμ` is a continuous linear
equivalence of the zero-mass signed measures, and `‖ν - μ‖_TV ≤ C ‖ν - Pν‖_TV` for
`ν` in a total-variation ball around `μ`.  The Fredholm alternative is applied on the
complete space of bounded continuous functions, since `SMeas d` is not complete.
-/

open MeasureTheory VectorMeasure Set
open scoped BoundedContinuousFunction

namespace DGPS.Structural

variable {d : ℕ}

theorem integral_withDensity_ofReal {g f : Torus d → ℝ} (hg : Continuous g) :
    ∫ x, f x ∂((haar d).withDensity fun x => ENNReal.ofReal (g x)) =
      ∫ x, max (g x) 0 * f x ∂haar d := by
  rw [integral_withDensity_eq_integral_toReal_smul
    hg.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal']

/-- Integration against `g m`: `∫ f d(g m) = ∫ f g dm`. -/
theorem integral_ofDensity {g f : Torus d → ℝ} (hg : Continuous g) (hf : Continuous f) :
    (ofDensity g).integral f = ∫ x, f x * g x ∂haar d := by
  have hi := integrable_of_cont hg
  have := isFiniteMeasure_withDensity_ofReal (μ := haar d) hi.2
  have : IsFiniteMeasure ((haar d).withDensity fun x => ENNReal.ofReal (-g x)) :=
    isFiniteMeasure_withDensity_ofReal (μ := haar d) hi.neg.2
  have e : ofDensity g =
      SMeas.ofMeasure ((haar d).withDensity fun x => ENNReal.ofReal (g x)) -
        SMeas.ofMeasure ((haar d).withDensity fun x => ENNReal.ofReal (-g x)) := by
    unfold ofDensity SMeas.ofMeasure
    rw [← map_sub]
    congr 1
    exact withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hi
  rw [e, SMeas.integral_sub_left _ _ hf, SMeas.integral_ofMeasure, SMeas.integral_ofMeasure,
    integral_withDensity_ofReal hg, integral_withDensity_ofReal (g := fun x => -g x) hg.neg]
  have h1 : Integrable (fun x => max (g x) 0 * f x) (haar d) :=
    integrable_of_cont ((hg.max continuous_const).mul hf)
  have h2 : Integrable (fun x => max (-g x) 0 * f x) (haar d) :=
    integrable_of_cont ((hg.neg.max continuous_const).mul hf)
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← sub_mul]
  have : max (g x) 0 - max (-g x) 0 = g x := by
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  rw [this]; ring


section Frozen

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem frozenWeight_q_pos (x : Torus d) : 0 < (frozenWeight A μ).q x :=
  lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1

/-- Injectivity of `I - DPμ`: a fixed vector of the derivative vanishes under coercivity. -/
theorem frozenGibbsDeriv_fixed_eq_zero (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hH : IsCoerciveDensityHessian A μ) (η : zeroMass d) (h : frozenGibbsDeriv A μ η = η) :
    η = 0 := by
  obtain ⟨c, hc, hcoer⟩ := hH
  set q := (frozenWeight A μ).q with hq
  have hd := (frozenGibbs_fderiv_signedMeasure A μ hμ).2.2.2 η
  rw [h] at hd
  have hηm := mem_zeroMass.1 η.2
  -- the continuous function `F = -K η`
  set F : Torus d → ℝ := fun x => -(η.1.integral fun y => centeredKernel A μ x y) with hFdef
  have hF : Continuous F := by
    have : F = fun x => -(wConv A η.1 x - η.1.integral (interactionConvolution A μ)) := by
      funext x
      simp only [hFdef]
      rw [integral_centeredKernel_eq A μ η.1 η.2 x]
    rw [this]
    exact (continuous_wConv A η.1).sub continuous_const |>.neg
  have hqc : Continuous q := (frozenWeight A μ).cont
  have hηeq : η.1 = ofDensity (fun x => q x * F x) := by
    have hfun : (fun x => q x * F x) = fun x =>
        -(frozenGibbs A μ).density x * ∫ᵛ y, centeredKernel A μ x y ∂•(SMeas.equiv η.1) := by
      funext x
      have e : (frozenGibbs A μ).density x = q x := rfl
      rw [e]
      simp only [hFdef, SMeas.integral]
      ring
    unfold ofDensity
    rw [hfun, ← hd, LinearEquiv.symm_apply_apply]
  -- the fixed-point equation `F = -T F` pointwise
  have hFeq : ∀ x, F x = -∫ y, centeredKernel A μ x y * F y ∂(μ : Measure (Torus d)) := by
    intro x
    have h1 : η.1.integral (fun y => centeredKernel A μ x y) =
        ∫ y, centeredKernel A μ x y * (q y * F y) ∂haar d := by
      conv_lhs => rw [hηeq]
      exact integral_ofDensity (hqc.mul hF) (continuous_kernelSection A μ x)
    have h2 := integral_eq_weight A μ hμ (fun y => centeredKernel A μ x y * F y)
    have h3 : (fun y => q y * (centeredKernel A μ x y * F y)) =
        fun y => centeredKernel A μ x y * (q y * F y) := by funext y; ring
    simp only [← hq] at h2
    rw [h3] at h2
    show -(η.1.integral fun y => centeredKernel A μ x y) = _
    rw [h1, ← h2]
  let Fb : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  let f : Lp ℝ 2 (μ : Measure (Torus d)) :=
    BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ Fb
  have hfae : (f : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] F :=
    BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus d)) ℝ Fb
  have hint0 : ∫ x, q x * F x ∂haar d = 0 := by
    rw [← equiv_ofDensity_univ (g := fun x => q x * F x) (hqc.mul hF), ← hηeq]
    exact hηm
  have hfmem : f ∈ centeredL2 μ := by
    show ∫ x, f x ∂(μ : Measure (Torus d)) = 0
    rw [integral_congr_ae hfae, integral_eq_weight A μ hμ F]
    exact hint0
  let f' : centeredL2 μ := ⟨f, hfmem⟩
  have hHf : densityHessian A μ f' = 0 := by
    apply Subtype.ext
    show f + kernelOp A μ f = 0
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add f (kernelOp A μ f), kernelOp_ae A μ f, hfae,
      Lp.coeFn_zero ℝ 2 (μ : Measure (Torus d))] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    unfold kernelTransform
    have : ∫ y, centeredKernel A μ x y * f y ∂(μ : Measure (Torus d)) =
        ∫ y, centeredKernel A μ x y * F y ∂(μ : Measure (Torus d)) :=
      integral_congr_ae (hfae.mono fun y hy => by simp only [hy])
    rw [this, hFeq x]
    simp
  have hnorm := hcoer f'
  rw [hHf, inner_zero_right] at hnorm
  have hf0 : f' = 0 := by
    have : ‖f'‖ ^ 2 ≤ 0 := by nlinarith
    have h0 : ‖f'‖ = 0 := by nlinarith [norm_nonneg f']
    exact norm_eq_zero.1 h0
  have hF0 : F =ᵐ[(μ : Measure (Torus d))] 0 := by
    have h1 : f = 0 := congrArg Subtype.val hf0
    filter_upwards [hfae, Lp.coeFn_zero ℝ 2 (μ : Measure (Torus d))] with x h2 h3
    rw [← h2, h1, h3]
  have hnη : ‖η.1‖ = 0 := by
    rw [hηeq, norm_ofDensity (g := fun x => q x * F x) (hqc.mul hF)]
    have : ∀ x, |q x * F x| = q x * |F x| := fun x => by
      rw [abs_mul, abs_of_pos (frozenWeight_q_pos A μ x)]
    simp_rw [this]
    rw [← integral_eq_weight A μ hμ (fun x => |F x|)]
    exact integral_eq_zero_of_ae (hF0.mono fun x hx => by simp [hx])
  exact Subtype.ext (norm_eq_zero.1 hnη)

/-- The map `g ↦ q (∫ q g − g) m`, with codomain `X = zeroMass d`. -/
noncomputable def frozenPhi : (Torus d →ᵇ ℝ) →L[ℝ] zeroMass d :=
  ((frozenWeight A μ).PhiS).codRestrict (zeroMass d) fun g => by
    show ofDensity ((frozenWeight A μ).phiDens g) ∈ zeroMass d
    rw [mem_zeroMass, equiv_ofDensity_univ ((frozenWeight A μ).phiDens_cont _)]
    exact (frozenWeight A μ).integral_phiDens _

/-- The map `η ↦ W * η` from `X` into bounded continuous functions. -/
noncomputable def frozenConv : zeroMass d →L[ℝ] (Torus d →ᵇ ℝ) :=
  (convCLM A).comp (zeroMass d).subtypeL

theorem frozenGibbsDeriv_eq_comp :
    frozenGibbsDeriv A μ = (frozenPhi A μ).comp (frozenConv A) := rfl

theorem isCompactOperator_frozenConv : IsCompactOperator (frozenConv A) :=
  (isCompactOperator_convCLM A).comp_clm (zeroMass d).subtypeL

/-- **STR006, invertibility.** If `μ = Pμ` and the density Hessian is coercive, then `I - DPμ`
is invertible on `X = zeroMass d`, with a bounded inverse. -/
theorem frozenLinearization_invertible (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hH : IsCoerciveDensityHessian A μ) :
    ∃ e : zeroMass d ≃L[ℝ] zeroMass d, ∀ η, e η = η - frozenGibbsDeriv A μ η := by
  set Φ := frozenPhi A μ with hΦ
  set C := frozenConv A with hC
  set E : (Torus d →ᵇ ℝ) →L[ℝ] (Torus d →ᵇ ℝ) := C.comp Φ with hE
  have hEc : IsCompactOperator E := (isCompactOperator_frozenConv A).comp_clm Φ
  have hD : ∀ η, frozenGibbsDeriv A μ η = Φ (C η) := fun η => rfl
  have hunit : IsUnit ((1 : (Torus d →ᵇ ℝ) →L[ℝ] (Torus d →ᵇ ℝ)) - E) := by
    rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (T := E) (μ := (1 : ℝ)) hEc
        one_ne_zero with h | h
    · exfalso
      obtain ⟨g, hg⟩ := h.exists_hasEigenvector
      have hg1 : E g = g := by simpa using hg.apply_eq_smul
      have hη : frozenGibbsDeriv A μ (Φ g) = Φ g := by
        rw [hD]
        show Φ (E g) = Φ g
        rw [hg1]
      have h0 := frozenGibbsDeriv_fixed_eq_zero A μ hμ hH _ hη
      apply hg.2
      rw [← hg1]
      show C (Φ g) = 0
      rw [h0, C.map_zero]
    · simpa [spectrum.mem_resolventSet_iff] using h
  obtain ⟨u, hu⟩ := hunit
  set R : (Torus d →ᵇ ℝ) →L[ℝ] (Torus d →ᵇ ℝ) := ↑u⁻¹ with hRdef
  have hl : ∀ y, R (y - E y) = y := fun y => by
    have h1 : (u⁻¹ : ((Torus d →ᵇ ℝ) →L[ℝ] (Torus d →ᵇ ℝ))ˣ).val * u.val = 1 := u.inv_mul
    have := congrArg (fun T => T y) h1
    simpa [hu] using this
  have hr : ∀ y, R y - E (R y) = y := fun y => by
    have h1 : u.val * (u⁻¹ : ((Torus d →ᵇ ℝ) →L[ℝ] (Torus d →ᵇ ℝ))ˣ).val = 1 := u.mul_inv
    have := congrArg (fun T => T y) h1
    simpa [hu] using this
  refine ⟨ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.id ℝ (zeroMass d) - frozenGibbsDeriv A μ)
    (ContinuousLinearMap.id ℝ (zeroMass d) + Φ.comp (R.comp C)) ?_ ?_, fun η => rfl⟩
  · intro η
    show (η - Φ (C η)) + Φ (R (C (η - Φ (C η)))) = η
    have hC1 : C (η - Φ (C η)) = C η - E (C η) := by rw [C.map_sub]; rfl
    rw [hC1, hl]
    abel
  · intro x
    show (x + Φ (R (C x))) - Φ (C (x + Φ (R (C x)))) = x
    have hC1 : C (x + Φ (R (C x))) = C x + E (R (C x)) := by rw [C.map_add]; rfl
    have h2 : C x + E (R (C x)) = R (C x) := (sub_eq_iff_eq_add.1 (hr (C x))).symm
    rw [hC1, h2]
    abel

theorem ofMeasure_congr {ρ σ : Measure (Torus d)} [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (h : ρ = σ) : SMeas.ofMeasure ρ = SMeas.ofMeasure σ := by
  subst h
  rfl

theorem norm_ofMeasure_sub (ρ σ : Measure (Torus d)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    ‖SMeas.ofMeasure ρ - SMeas.ofMeasure σ‖ = fullVariation ρ σ := by
  rw [← norm_toSignedMeasure_sub, SMeas.ofMeasure, SMeas.ofMeasure, map_sub]

theorem ofMeasure_sub_mem_zeroMass (ρ σ : Measure (Torus d)) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure σ] : SMeas.ofMeasure ρ - SMeas.ofMeasure σ ∈ zeroMass d := by
  rw [mem_zeroMass]
  unfold SMeas.ofMeasure
  rw [← map_sub, LinearEquiv.apply_symm_apply]
  rw [sub_apply, Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ]
  simp

/-- **STR006, local residual estimate.**  If `μ = Pμ` and the density Hessian is coercive,
there are `δ > 0` and `C_loc` such that every probability `ν` with `‖ν - μ‖_TV ≤ δ` satisfies
`‖ν - μ‖_TV ≤ C_loc ‖ν - Pν‖_TV` (full total variation). -/
theorem frozenResidual_local_errorBound (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hH : IsCoerciveDensityHessian A μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ProbabilityMeasure (Torus d),
      fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤ δ →
        fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤
          C * fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure := by
  obtain ⟨e, he⟩ := frozenLinearization_invertible A μ hμ hH
  obtain ⟨Cq, r, hr, -, hq⟩ := frozenGibbs_quadratic_remainder A μ
  set M : ℝ := ‖(e.symm : zeroMass d →L[ℝ] zeroMass d)‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg (e.symm : zeroMass d →L[ℝ] zeroMass d)
  have hK0 : 0 ≤ M * |Cq| := mul_nonneg hM0 (abs_nonneg _)
  refine ⟨min r (1 / (2 * (M * |Cq| + 1))), lt_min hr (by positivity), 2 * M,
    by positivity, fun ν hν => ?_⟩
  set δ := min r (1 / (2 * (M * |Cq| + 1))) with hδ
  have hδr : δ ≤ r := min_le_left _ _
  have hδ2 : δ * (2 * (M * |Cq| + 1)) ≤ 1 := by
    have := min_le_right r (1 / (2 * (M * |Cq| + 1)))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hδ0 : 0 ≤ δ := le_min hr.le (by positivity)
  set η : zeroMass d := ⟨SMeas.ofMeasure (ν : Measure (Torus d)) -
    SMeas.ofMeasure (μ : Measure (Torus d)), ofMeasure_sub_mem_zeroMass _ _⟩ with hη
  have hηn : ‖η‖ = fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) :=
    norm_ofMeasure_sub _ _
  have hηδ : ‖η‖ ≤ δ := hηn ▸ hν
  have hrem := hq ν η rfl (hηδ.trans hδr)
  have hPμ : SMeas.ofMeasure (frozenGibbs A μ).measure = SMeas.ofMeasure (μ : Measure (Torus d)) :=
    ofMeasure_congr hμ
  rw [hPμ] at hrem
  set ρ : SMeas d := SMeas.ofMeasure (ν : Measure (Torus d)) -
    SMeas.ofMeasure (frozenGibbs A ν).measure with hρ
  have hρn : ‖ρ‖ = fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure :=
    norm_ofMeasure_sub _ _
  have hid : (e η).1 = ρ + (SMeas.ofMeasure (frozenGibbs A ν).measure -
      SMeas.ofMeasure (μ : Measure (Torus d)) - (frozenGibbsDeriv A μ η).1) := by
    rw [he η]
    show η.1 - (frozenGibbsDeriv A μ η).1 = _
    simp only [hη, hρ]
    abel
  have h1 : ‖η‖ ≤ M * ‖e η‖ := by
    have := (e.symm : zeroMass d →L[ℝ] zeroMass d).le_opNorm (e η)
    simpa [hM] using this
  have h2 : ‖e η‖ ≤ ‖ρ‖ + Cq * ‖η‖ ^ 2 := by
    calc ‖e η‖ = ‖(e η).1‖ := rfl
      _ = _ := by rw [hid]
      _ ≤ ‖ρ‖ + ‖SMeas.ofMeasure (frozenGibbs A ν).measure -
          SMeas.ofMeasure (μ : Measure (Torus d)) - (frozenGibbsDeriv A μ η).1‖ := norm_add_le _ _
      _ ≤ ‖ρ‖ + Cq * ‖η‖ ^ 2 := by linarith
  have h3 : ‖η‖ ≤ M * (‖ρ‖ + Cq * ‖η‖ ^ 2) := h1.trans (mul_le_mul_of_nonneg_left h2 hM0)
  have ht0 : 0 ≤ ‖η‖ := norm_nonneg _
  have h4 : M * (Cq * ‖η‖ ^ 2) ≤ (M * |Cq|) * (δ * ‖η‖) := by
    have : Cq * ‖η‖ ^ 2 ≤ |Cq| * (δ * ‖η‖) := by
      calc Cq * ‖η‖ ^ 2 ≤ |Cq| * ‖η‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Cq| * (δ * ‖η‖) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          nlinarith
    calc M * (Cq * ‖η‖ ^ 2) ≤ M * (|Cq| * (δ * ‖η‖)) := mul_le_mul_of_nonneg_left this hM0
      _ = _ := by ring
  have h5 : (M * |Cq|) * (δ * ‖η‖) ≤ ‖η‖ / 2 := by
    have : (M * |Cq|) * δ ≤ 1 / 2 := by nlinarith
    nlinarith
  rw [← hηn, ← hρn]
  nlinarith

end Frozen

end DGPS.Structural
