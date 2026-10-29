import SharpSymmetricLSI.Infra.Mollify

/-!
# Weak gradients: closedness, algebra and the chain rule (Phase 2, I1, milestone 2)

* `isWeakGrad_of_tendsto`: weak-gradient pairs converging in `L¹(m)` have a weak-gradient pair as
  limit.
* `IsWeakGrad.add`, `isWeakGrad_const`, `IsWeakGrad.cmul`, `IsWeakGrad.sub_const`.
* `isWeakGrad_comp`: chain rule for `C¹` functions with bounded derivative.
* `isWeakGrad_comp_limit`: the chain rule passed to limits of such functions.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

theorem exists_cube_of_hasCompactSupport {ψ : (ι → ℝ) → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ R : ℕ, tsupport ψ ⊆ cube ι R := by
  obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_ge r
  refine ⟨n, fun x hx => ?_⟩
  have := hr hx
  simp only [Metric.mem_closedBall, dist_zero_right] at this
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Icc]
  intro i
  have := (norm_le_pi_norm x i).trans (this.trans hn)
  rw [Real.norm_eq_abs] at this
  exact abs_le.mp this

/-- `L¹(m)` convergence on the torus gives convergence of the integrals of lifts against
compactly supported continuous functions on `ℝ^ι`. -/
theorem tendsto_integral_lift_mul {u : ℕ → UnitAddTorus ι → ℝ} {u₀ : UnitAddTorus ι → ℝ}
    (hu : ∀ n, Integrable (u n) volume) (hu₀ : Integrable u₀ volume)
    (h : Tendsto (fun n => ∫⁻ y, ‖u n y - u₀ y‖ₑ) atTop (𝓝 0)) {ψ : (ι → ℝ) → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x, u n (liftT x) * ψ x) atTop (𝓝 (∫ x, u₀ (liftT x) * ψ x)) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψc
  obtain ⟨R, hR⟩ := exists_cube_of_hasCompactSupport hψc
  have hint : ∀ v : UnitAddTorus ι → ℝ, Integrable v volume →
      Integrable (fun x => v (liftT x) * ψ x) volume := fun v hv =>
    (locallyIntegrable_comp_liftT hv).integrable_smul_right_of_hasCompactSupport hψ hψc
  rw [tendsto_iff_edist_tendsto_0]
  set K : ℝ≥0∞ := ENNReal.ofReal C * ((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι
  have hbound : ∀ n, edist (∫ x, u n (liftT x) * ψ x) (∫ x, u₀ (liftT x) * ψ x) ≤
      K * ∫⁻ y, ‖u n y - u₀ y‖ₑ := by
    intro n
    rw [edist_eq_enorm_sub, ← integral_sub (hint _ (hu n)) (hint _ hu₀)]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ x, ‖u n (liftT x) * ψ x - u₀ (liftT x) * ψ x‖ₑ
        ≤ ∫⁻ x, (cube ι R).indicator
            (fun x => ‖u n (liftT x) - u₀ (liftT x)‖ₑ * ENNReal.ofReal C) x := by
          refine lintegral_mono fun x => ?_
          rw [← sub_mul, enorm_mul]
          by_cases hx : x ∈ cube ι R
          · rw [indicator_of_mem hx]
            gcongr
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC x)
          · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hR h))
            simp [this]
      _ = (∫⁻ x in cube ι R, ‖u n (liftT x) - u₀ (liftT x)‖ₑ) * ENNReal.ofReal C := by
          rw [lintegral_indicator (show MeasurableSet (cube ι R) from
              MeasurableSet.univ_pi fun _ => measurableSet_Icc),
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ y, ‖u n y - u₀ y‖ₑ) *
            ENNReal.ofReal C := by
          gcongr
          exact lintegral_cube_le (H := fun y => ‖u n y - u₀ y‖ₑ) R
            ((hu n).aestronglyMeasurable.sub hu₀.aestronglyMeasurable).enorm
      _ = K * ∫⁻ y, ‖u n y - u₀ y‖ₑ := by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
    hbound
  have := ENNReal.Tendsto.const_mul (a := K) h (Or.inr
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))))
  simpa using this

variable [DecidableEq ι]

/-- **Closedness.** Weak-gradient pairs converging in `L¹(m)` converge to a weak-gradient pair. -/
theorem isWeakGrad_of_tendsto {F : ℕ → UnitAddTorus ι → ℝ} {G : ℕ → UnitAddTorus ι → ι → ℝ}
    {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ} (hFG : ∀ n, IsWeakGrad (F n) (G n))
    (hFi : ∀ n, Integrable (F n) volume) (hGi : ∀ n k, Integrable (fun y => G n y k) volume)
    (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    (hF : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ) atTop (𝓝 0))
    (hG : ∀ k, Tendsto (fun n => ∫⁻ y, ‖G n y k - g y k‖ₑ) atTop (𝓝 0)) :
    IsWeakGrad f g := by
  refine ⟨locallyIntegrable_comp_liftT hf, fun k => locallyIntegrable_comp_liftT (hg k),
    fun φ hφ hφc k => ?_⟩
  have hφ' : Continuous fun x => fderiv ℝ φ x (Pi.single k 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 := tendsto_integral_lift_mul hFi hf hF hφ' (hφc.fderiv_apply (𝕜 := ℝ) _)
  have h2 := tendsto_integral_lift_mul (fun n => hGi n k) (hg k) (hG k) hφ.continuous hφc
  have heq : ∀ n, ∫ x, F n (liftT x) * fderiv ℝ φ x (Pi.single k 1) =
      -∫ x, G n (liftT x) k * φ x := fun n => (hFG n).ibp φ hφ hφc k
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2.neg

theorem integral_fderiv_eq_zero {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (v : ι → ℝ) : ∫ x, fderiv ℝ φ x v = 0 := by
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : ι → ℝ => (1 : ℝ)) (g := φ) (v := v)
    (by simp) (by simpa using ((hφ.continuous_fderiv (by simp)).clm_apply
      continuous_const).integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) v))
    (by simpa using hφ.continuous.integrable_of_hasCompactSupport hφc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hφ.differentiable (by simp)) x)
  simpa using this

theorem isWeakGrad_const (c : ℝ) : IsWeakGrad (fun _ : UnitAddTorus ι => c) 0 := by
  refine ⟨locallyIntegrable_const c, fun k => by simpa using locallyIntegrable_const (0 : ℝ),
    fun φ hφ hφc k => ?_⟩
  simp only [Function.comp, Pi.zero_apply, zero_mul, integral_zero, neg_zero]
  rw [integral_const_mul, integral_fderiv_eq_zero hφ hφc, mul_zero]

theorem IsWeakGrad.add {f₁ f₂ : UnitAddTorus ι → ℝ} {g₁ g₂ : UnitAddTorus ι → ι → ℝ}
    (h₁ : IsWeakGrad f₁ g₁) (h₂ : IsWeakGrad f₂ g₂) :
    IsWeakGrad (fun y => f₁ y + f₂ y) (fun y k => g₁ y k + g₂ y k) := by
  refine ⟨h₁.locInt.add h₂.locInt, fun k => (h₁.locInt_grad k).add (h₂.locInt_grad k),
    fun φ hφ hφc k => ?_⟩
  have hφ' : Continuous fun x => fderiv ℝ φ x (Pi.single k 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 := h₁.locInt.integrable_smul_right_of_hasCompactSupport hφ' (hφc.fderiv_apply (𝕜 := ℝ) _)
  have i2 := h₂.locInt.integrable_smul_right_of_hasCompactSupport hφ' (hφc.fderiv_apply (𝕜 := ℝ) _)
  have j1 := (h₁.locInt_grad k).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have j2 := (h₂.locInt_grad k).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  simp only [smul_eq_mul, Function.comp] at i1 i2 j1 j2
  simp only [Function.comp, add_mul]
  rw [integral_add i1 i2, integral_add j1 j2, h₁.ibp φ hφ hφc k, h₂.ibp φ hφ hφc k, neg_add]

theorem IsWeakGrad.cmul {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (c : ℝ) : IsWeakGrad (fun x => c * f x) (fun x k => c * g x k) := by
  refine ⟨h.locInt.smul c, fun k => (h.locInt_grad k).smul c, fun φ hφ hφc k => ?_⟩
  simp only [Function.comp, mul_assoc]
  rw [integral_const_mul, integral_const_mul, h.ibp φ hφ hφc k, mul_neg]

theorem IsWeakGrad.sub_const {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (c : ℝ) : IsWeakGrad (fun y => f y - c) g := by
  have := h.add (isWeakGrad_const (-c))
  simpa [sub_eq_add_neg] using this

/-! ### The chain rule -/

omit [DecidableEq ι] in
theorem integrable_moll (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    Integrable (moll n u) volume :=
  ⟨(measurable_moll n hu).aestronglyMeasurable, (lintegral_moll_le n hu).trans_lt hu.2⟩

theorem lipschitz_of_deriv_le {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ}
    (hL : ∀ t, |deriv G t| ≤ L) (a b : ℝ) : |G a - G b| ≤ L * |a - b| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := G) (C := L)
    (fun x _ => (hG.differentiable one_ne_zero) x) (fun x _ => by rw [Real.norm_eq_abs]; exact hL x)
    convex_univ (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

omit [DecidableEq ι] in
theorem integrable_comp_of_lipschitz {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ}
    (hL : ∀ t, |deriv G t| ≤ L) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) :
    Integrable (fun y => G (u y)) volume := by
  refine Integrable.mono' ((integrable_const |G 0|).add (hu.norm.const_mul L))
    (hG.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have := lipschitz_of_deriv_le hG hL (u y) 0
  simp only [sub_zero, Real.norm_eq_abs] at this ⊢
  have h2 := abs_sub_abs_le_abs_sub (G (u y)) (G 0)
  show |G (u y)| ≤ |G 0| + L * |u y|
  linarith

/-- `∫⁻ ‖G ∘ u - G ∘ v‖ ≤ L ∫⁻ ‖u - v‖`. -/
theorem lintegral_comp_sub_le {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ}
    (hL : ∀ t, |deriv G t| ≤ L) (u v : UnitAddTorus ι → ℝ) :
    ∫⁻ y, ‖G (u y) - G (v y)‖ₑ ≤ ENNReal.ofReal L * ∫⁻ y, ‖u y - v y‖ₑ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hL0]
  exact ENNReal.ofReal_le_ofReal (by
    simpa [Real.norm_eq_abs] using lipschitz_of_deriv_le hG hL (u y) (v y))

/-- **Chain rule** for `C¹` functions with bounded derivative. -/
theorem isWeakGrad_comp {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ} (hL : ∀ t, |deriv G t| ≤ L) :
    IsWeakGrad (fun y => G (f y)) (fun y k => deriv G (f y) * g y k) := by
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0)
  have hG' : Continuous (deriv G) := hG.continuous_deriv le_rfl
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (measurable_moll n hf).aestronglyMeasurable) hf.aestronglyMeasurable
    (tendsto_moll hf)
  set F : ℕ → UnitAddTorus ι → ℝ := fun j => moll (ns j) f with hFdef
  set Gr : ℕ → UnitAddTorus ι → ι → ℝ := fun j y k => moll (ns j) (fun z => g z k) y with hGrdef
  -- the approximating pairs
  have hpair : ∀ j, IsWeakGrad (fun y => G (F j y)) (fun y k => deriv G (F j y) * Gr j y k) := by
    intro j
    have hs : ContDiff ℝ 1 ((fun y => G (F j y)) ∘ liftT) :=
      hG.comp ((moll_comp_liftT_contDiff (ns j) hf).of_le (by simp))
    have hc := isWeakGrad_of_contDiff hs
    convert hc using 1
    funext y k
    have hΦ : HasFDerivAt (F j ∘ liftT) (fderiv ℝ (F j ∘ liftT) (secT y)) (secT y) :=
      (((moll_comp_liftT_contDiff (ns j) hf).differentiable (by simp)) (secT y)).hasFDerivAt
    have hcomp := (((hG.differentiable one_ne_zero) ((F j ∘ liftT) (secT y))).hasDerivAt).comp_hasFDerivAt
      (secT y) hΦ
    rw [show ((fun y => G (F j y)) ∘ liftT) = G ∘ (F j ∘ liftT) from rfl, hcomp.fderiv]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Function.comp_apply, liftT_secT]
    congr 1
    rw [hFdef]; simp only
    rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h (ns j) (secT y) k]
    rfl
  have hFi : ∀ j, Integrable (F j) volume := fun j => integrable_moll (ns j) hf
  have hGri : ∀ j k, Integrable (fun y => Gr j y k) volume := fun j k => integrable_moll (ns j) (hg k)
  have hbdd : ∀ u : UnitAddTorus ι → ℝ, AEStronglyMeasurable u volume →
      ∀ v : UnitAddTorus ι → ℝ, Integrable v volume →
      Integrable (fun y => deriv G (u y) * v y) volume := fun u hu v hv =>
    hv.bdd_mul (hG'.comp_aestronglyMeasurable hu)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hL _)
  refine isWeakGrad_of_tendsto hpair (fun j => integrable_comp_of_lipschitz hG hL (hFi j))
    (fun j k => hbdd _ (hFi j).aestronglyMeasurable _ (hGri j k))
    (integrable_comp_of_lipschitz hG hL hf) (fun k => hbdd _ hf.aestronglyMeasurable _ (hg k))
    ?_ (fun k => ?_)
  · -- `G ∘ F_j → G ∘ f`
    have h0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L)
      ((tendsto_moll hf).comp hns.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun j => zero_le)
      (fun j => lintegral_comp_sub_le hG hL _ _)
  · -- `G'(F_j) ∇F_j → G'(f) ∇f`
    have hA := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L)
      ((tendsto_moll (hg k)).comp hns.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hA
    have hB : Tendsto (fun j => ∫⁻ y, ‖(deriv G (F j y) - deriv G (f y)) * g y k‖ₑ) atTop
        (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence' (μ := volume)
        (F := fun j y => ‖(deriv G (F j y) - deriv G (f y)) * g y k‖ₑ) (f := fun _ => 0)
        (fun y => ENNReal.ofReal (2 * L) * ‖g y k‖ₑ)
        (fun j => (((hG'.comp_aestronglyMeasurable (hFi j).aestronglyMeasurable).sub
          (hG'.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mul
          (hg k).aestronglyMeasurable).enorm)
        (fun j => Eventually.of_forall fun y => by
          dsimp only
          rw [enorm_mul, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
            ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs]
          calc |deriv G (F j y) - deriv G (f y)| ≤ |deriv G (F j y)| + |deriv G (f y)| :=
                abs_sub _ _
            _ ≤ 2 * L := by linarith [hL (F j y), hL (f y)])
        (by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hg k).2.ne)
        (by
          filter_upwards [hae] with y hy
          have : Tendsto (fun j => (deriv G (F j y) - deriv G (f y)) * g y k) atTop
              (𝓝 ((deriv G (f y) - deriv G (f y)) * g y k)) :=
            (((hG'.tendsto _).comp hy).sub tendsto_const_nhds).mul tendsto_const_nhds
          rw [sub_self, zero_mul] at this
          have h2 := (continuous_enorm.tendsto (0 : ℝ)).comp this
          rw [enorm_zero] at h2
          exact h2)
      simpa using this
    have hsum := hA.add hB
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun j => zero_le)
      (fun j => ?_)
    have hm1 : AEMeasurable (fun y => ENNReal.ofReal L * ‖Gr j y k - g y k‖ₑ) volume :=
      (((hGri j k).aestronglyMeasurable.sub (hg k).aestronglyMeasurable).enorm).const_mul _
    calc ∫⁻ y, ‖deriv G (F j y) * Gr j y k - deriv G (f y) * g y k‖ₑ
        ≤ ∫⁻ y, (ENNReal.ofReal L * ‖Gr j y k - g y k‖ₑ +
            ‖(deriv G (F j y) - deriv G (f y)) * g y k‖ₑ) := by
          refine lintegral_mono fun y => ?_
          have e : deriv G (F j y) * Gr j y k - deriv G (f y) * g y k =
              deriv G (F j y) * (Gr j y k - g y k) + (deriv G (F j y) - deriv G (f y)) * g y k :=
            by ring
          rw [e]
          refine (enorm_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [enorm_mul, ← ofReal_norm (deriv G (F j y))]
          gcongr
          rw [Real.norm_eq_abs]; exact hL _
      _ = ENNReal.ofReal L * (∫⁻ y, ‖Gr j y k - g y k‖ₑ) +
            ∫⁻ y, ‖(deriv G (F j y) - deriv G (f y)) * g y k‖ₑ := by
          rw [lintegral_add_left' hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := rfl

/-- The chain rule passed to limits: `G_j → G` uniformly, `G_j' → D` pointwise, `|G_j'| ≤ L`. -/
theorem isWeakGrad_comp_limit {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    {Gs : ℕ → ℝ → ℝ} (hGs : ∀ j, ContDiff ℝ 1 (Gs j)) {L : ℝ} (hL : ∀ j t, |deriv (Gs j) t| ≤ L)
    {G D : ℝ → ℝ} (hGc : Continuous G) (hDm : Measurable D)
    (hunif : ∀ ε > 0, ∀ᶠ j in atTop, ∀ t, |Gs j t - G t| ≤ ε)
    (hD : ∀ t, Tendsto (fun j => deriv (Gs j) t) atTop (𝓝 (D t))) :
    IsWeakGrad (fun y => G (f y)) (fun y k => D (f y) * g y k) := by
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0 0)
  have hDL : ∀ t, |D t| ≤ L := fun t =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hD t)) fun j => hL j t
  have hGsi : ∀ j, Integrable (fun y => Gs j (f y)) volume := fun j =>
    integrable_comp_of_lipschitz (hGs j) (hL j) hf
  obtain ⟨j₀, hj₀⟩ := (hunif 1 one_pos).exists
  have hGi : Integrable (fun y => G (f y)) volume := by
    refine Integrable.mono' ((hGsi j₀).norm.add (integrable_const 1))
      (hGc.comp_aestronglyMeasurable hf.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    have := hj₀ (f y)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    have h2 := abs_sub_abs_le_abs_sub (G (f y)) (Gs j₀ (f y))
    rw [abs_sub_comm] at this
    linarith
  have hbddD : ∀ k, Integrable (fun y => D (f y) * g y k) volume := fun k =>
    (hg k).bdd_mul (hDm.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hDL _)
  refine isWeakGrad_of_tendsto (fun j => isWeakGrad_comp h hf hg (hGs j) (hL j)) hGsi
    (fun j k => (hg k).bdd_mul (((hGs j).continuous_deriv le_rfl).comp_aestronglyMeasurable
      hf.aestronglyMeasurable) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hL j _))
    hGi hbddD ?_ (fun k => ?_)
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεt : ε = ⊤
    · exact Eventually.of_forall fun j => by rw [hεt]; exact le_top
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    filter_upwards [hunif _ hεr] with j hj
    calc ∫⁻ y, ‖Gs j (f y) - G (f y)‖ₑ ≤ ∫⁻ _y, ENNReal.ofReal ε.toReal :=
          lintegral_mono fun y => by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (by
              rw [Real.norm_eq_abs]; exact hj _)
      _ = ε := by rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_toReal hεt]
  · have := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun j y => ‖deriv (Gs j) (f y) * g y k - D (f y) * g y k‖ₑ) (f := fun _ => 0)
      (fun y => ENNReal.ofReal (2 * L) * ‖g y k‖ₑ)
      (fun j => (((((hGs j).continuous_deriv le_rfl).comp_aestronglyMeasurable
        hf.aestronglyMeasurable).mul (hg k).aestronglyMeasurable).sub
        (hbddD k).aestronglyMeasurable).enorm)
      (fun j => Eventually.of_forall fun y => by
        dsimp only
        rw [← sub_mul, enorm_mul, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by linarith)]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [Real.norm_eq_abs]
        calc |deriv (Gs j) (f y) - D (f y)| ≤ |deriv (Gs j) (f y)| + |D (f y)| := abs_sub _ _
          _ ≤ 2 * L := by linarith [hL j (f y), hDL (f y)])
      (by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hg k).2.ne)
      (Eventually.of_forall fun y => by
        have h1 : Tendsto (fun j => deriv (Gs j) (f y) * g y k - D (f y) * g y k) atTop
            (𝓝 (D (f y) * g y k - D (f y) * g y k)) :=
          ((hD (f y)).mul tendsto_const_nhds).sub tendsto_const_nhds
        rw [sub_self] at h1
        have h2 := (continuous_enorm.tendsto (0 : ℝ)).comp h1
        rw [enorm_zero] at h2
        exact h2)
    simpa using this

/-! ### Smooth approximations of the positive part -/

/-- `S_{c,a}(t) = (√((t-c)² + a⁴) + (t - c))/2`, a smooth approximation of `t₊`. -/
noncomputable def posApprox (c a : ℝ) (t : ℝ) : ℝ :=
  (Real.sqrt ((t - c) ^ 2 + a ^ 4) + (t - c)) / 2

theorem hasDerivAt_posApprox {c a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (posApprox c a)
      (((t - c) / Real.sqrt ((t - c) ^ 2 + a ^ 4) + 1) / 2) t := by
  have hpos : 0 < (t - c) ^ 2 + a ^ 4 := by positivity
  have h1 : HasDerivAt (fun t => (t - c) ^ 2 + a ^ 4) (2 * (t - c)) t := by
    have := ((hasDerivAt_id t).sub_const c).pow 2
    simpa using this.add_const (a ^ 4)
  have h2 := (h1.sqrt hpos.ne').add ((hasDerivAt_id t).sub_const c)
  have h4 : HasDerivAt (posApprox c a)
      ((2 * (t - c) / (2 * Real.sqrt ((t - c) ^ 2 + a ^ 4)) + 1) / 2) t := h2.div_const 2
  convert h4 using 3
  rw [mul_div_mul_left _ _ two_ne_zero]

theorem contDiff_posApprox {c a : ℝ} (ha : a ≠ 0) : ContDiff ℝ 1 (posApprox c a) := by
  unfold posApprox
  have : ∀ t : ℝ, (t - c) ^ 2 + a ^ 4 ≠ 0 := fun t => by positivity
  fun_prop (disch := exact this _)

theorem deriv_posApprox {c a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    deriv (posApprox c a) t = ((t - c) / Real.sqrt ((t - c) ^ 2 + a ^ 4) + 1) / 2 :=
  (hasDerivAt_posApprox ha t).deriv

theorem abs_div_sqrt_le (s e : ℝ) : |s / Real.sqrt (s ^ 2 + e ^ 2)| ≤ 1 := by
  rcases eq_or_ne (s ^ 2 + e ^ 2) 0 with h | h
  · simp [h]
  · have hpos : 0 < Real.sqrt (s ^ 2 + e ^ 2) := Real.sqrt_pos.mpr (lt_of_le_of_ne (by positivity)
      (Ne.symm h))
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    calc |s| = Real.sqrt (s ^ 2) := (Real.sqrt_sq_eq_abs s).symm
      _ ≤ Real.sqrt (s ^ 2 + e ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

theorem abs_deriv_posApprox_le {c a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    |deriv (posApprox c a) t| ≤ 1 := by
  rw [deriv_posApprox ha]
  have := abs_div_sqrt_le (t - c) (a ^ 2)
  rw [show (a ^ 2) ^ 2 = a ^ 4 by ring] at this
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

theorem abs_posApprox_sub_le (c a t : ℝ) : |posApprox c a t - max t 0| ≤ a ^ 2 / 2 + |c| := by
  have hs : Real.sqrt ((t - c) ^ 2 + a ^ 4) - |t - c| ∈ Set.Icc 0 (a ^ 2) := by
    constructor
    · rw [sub_nonneg, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [pow_nonneg (sq_nonneg a) 2])
    · rw [sub_le_iff_le_add, ← Real.sqrt_sq (add_nonneg (sq_nonneg a) (abs_nonneg (t - c)))]
      apply Real.sqrt_le_sqrt
      nlinarith [abs_nonneg (t - c), sq_abs (t - c), sq_nonneg a]
  have hmax : |max (t - c) 0 - max t 0| ≤ |c| := by
    have := abs_max_sub_max_le_abs (t - c) t 0
    simpa [abs_sub_comm] using this
  have h1 : posApprox c a t - max (t - c) 0 = (Real.sqrt ((t - c) ^ 2 + a ^ 4) - |t - c|) / 2 := by
    unfold posApprox
    rcases le_total 0 (t - c) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  calc |posApprox c a t - max t 0|
      ≤ |posApprox c a t - max (t - c) 0| + |max (t - c) 0 - max t 0| := abs_sub_le _ _ _
    _ ≤ a ^ 2 / 2 + |c| := by
        rw [h1, abs_div, abs_of_nonneg hs.1, abs_two]
        linarith [hs.2]

/-- `a_j = 1/(j+1)`. -/
noncomputable def aSeq (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem aSeq_pos (j : ℕ) : 0 < aSeq j := by unfold aSeq; positivity

theorem tendsto_aSeq : Tendsto aSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Limit of `deriv S_{σa,a}(t)` as `a → 0`, `σ = ±1`. -/
theorem tendsto_deriv_posApprox (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (t : ℝ) :
    Tendsto (fun j => deriv (posApprox (σ * aSeq j) (aSeq j)) t) atTop
      (𝓝 (if 0 < t then 1 else if t < 0 then 0 else (1 - σ) / 2)) := by
  simp_rw [deriv_posApprox (aSeq_pos _).ne']
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hnum : Tendsto (fun j => t - σ * aSeq j) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.sub (tendsto_aSeq.const_mul σ)
    have hden : Tendsto (fun j => Real.sqrt ((t - σ * aSeq j) ^ 2 + aSeq j ^ 4)) atTop
        (𝓝 (Real.sqrt (t ^ 2 + 0 ^ 4))) :=
      ((hnum.pow 2).add (tendsto_aSeq.pow 4)).sqrt
    have hne : Real.sqrt (t ^ 2 + 0 ^ 4) ≠ 0 := by
      simp [Real.sqrt_eq_zero', ht.ne]
    have := ((hnum.div hden hne).add (tendsto_const_nhds (x := (1 : ℝ)))).div_const 2
    convert this using 2
    simp only [ht, not_lt.mpr ht.le, ↓reduceIte]
    rw [show (0 : ℝ) ^ 4 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs, abs_of_neg ht,
      div_neg, div_self ht.ne]
    ring
  · subst ht
    simp only [lt_irrefl, ↓reduceIte]
    have hs : ∀ j, (0 - σ * aSeq j) / Real.sqrt ((0 - σ * aSeq j) ^ 2 + aSeq j ^ 4) =
        -σ / Real.sqrt (1 + aSeq j ^ 2) := by
      intro j
      have ha := aSeq_pos j
      have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
      have : (0 - σ * aSeq j) ^ 2 + aSeq j ^ 4 = aSeq j ^ 2 * (1 + aSeq j ^ 2) := by
        rw [zero_sub, neg_sq, mul_pow, hσ2]; ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
      field_simp
      ring
    simp_rw [hs]
    have h1 : Tendsto (fun j => Real.sqrt (1 + aSeq j ^ 2)) atTop (𝓝 (Real.sqrt (1 + 0 ^ 2))) :=
      (tendsto_const_nhds.add (tendsto_aSeq.pow 2)).sqrt
    have := ((tendsto_const_nhds (x := -σ)).div h1 (by norm_num)).add (tendsto_const_nhds (x := (1 : ℝ)))
      |>.div_const 2
    convert this using 2
    norm_num
    ring
  · have hnum : Tendsto (fun j => t - σ * aSeq j) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.sub (tendsto_aSeq.const_mul σ)
    have hden : Tendsto (fun j => Real.sqrt ((t - σ * aSeq j) ^ 2 + aSeq j ^ 4)) atTop
        (𝓝 (Real.sqrt (t ^ 2 + 0 ^ 4))) :=
      ((hnum.pow 2).add (tendsto_aSeq.pow 4)).sqrt
    have hne : Real.sqrt (t ^ 2 + 0 ^ 4) ≠ 0 := by
      simp [Real.sqrt_eq_zero', ht.ne']
    have := ((hnum.div hden hne).add (tendsto_const_nhds (x := (1 : ℝ)))).div_const 2
    convert this using 2
    simp only [ht, ↓reduceIte]
    rw [show (0 : ℝ) ^ 4 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos ht,
      div_self ht.ne']
    norm_num

theorem abs_posApprox_aSeq_le (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (j : ℕ) (t : ℝ) :
    |posApprox (σ * aSeq j) (aSeq j) t - max t 0| ≤ aSeq j ^ 2 / 2 + aSeq j := by
  have := abs_posApprox_sub_le (σ * aSeq j) (aSeq j) t
  have hσa : |σ * aSeq j| = aSeq j := by
    rcases hσ with h | h <;> simp [h, abs_of_pos (aSeq_pos j)]
  rwa [hσa] at this

theorem eventually_posApprox_close (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ t, |posApprox (σ * aSeq j) (aSeq j) t - max t 0| ≤ ε := by
  have h : Tendsto (fun j => aSeq j ^ 2 / 2 + aSeq j) atTop (𝓝 (0 ^ 2 / 2 + 0)) :=
    ((tendsto_aSeq.pow 2).div_const 2).add tendsto_aSeq
  rw [show (0 : ℝ) ^ 2 / 2 + 0 = 0 by norm_num] at h
  filter_upwards [(tendsto_order.mp h).2 ε hε] with j hj t
  exact (abs_posApprox_aSeq_le σ hσ j t).trans hj.le

/-! ### Truncations -/

/-- The weak gradient of `f₊`, with the value `(1-σ)/2` of the derivative at `0`. -/
theorem isWeakGrad_max_zero_aux {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    IsWeakGrad (fun y => max (f y) 0)
      (fun y k => (if 0 < f y then 1 else if f y < 0 then 0 else (1 - σ) / 2) * g y k) := by
  refine isWeakGrad_comp_limit h hf hg (Gs := fun j => posApprox (σ * aSeq j) (aSeq j))
    (fun j => contDiff_posApprox (aSeq_pos j).ne') (L := 1)
    (fun j t => abs_deriv_posApprox_le (aSeq_pos j).ne' t) (continuous_id.max continuous_const)
    ?_ (fun ε hε => eventually_posApprox_close σ hσ hε) (tendsto_deriv_posApprox σ hσ)
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

/-- `∇f = 0` a.e. on `{f = 0}`. -/
theorem ae_grad_eq_zero_of_eq_zero {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume) :
    ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)), f y = 0 → ∀ k, g y k = 0 := by
  have h1 := isWeakGrad_max_zero_aux h hf hg 1 (Or.inl rfl)
  have h2 := isWeakGrad_max_zero_aux h hf hg (-1) (Or.inr rfl)
  filter_upwards [weakGrad_ae_unique h1 h2] with y hy hfy k
  have := congrFun hy k
  simp only [hfy, lt_irrefl, ↓reduceIte] at this
  norm_num at this
  linarith

/-- `∇f = 0` a.e. on `{f = M}`. -/
theorem ae_grad_eq_zero_of_eq {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    (M : ℝ) : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)), f y = M → ∀ k, g y k = 0 := by
  filter_upwards [ae_grad_eq_zero_of_eq_zero (h.sub_const M) (hf.sub (integrable_const M)) hg]
    with y hy hfy
  exact hy (by rw [hfy, sub_self])

/-- `∇(f - M)₊ = 1_{f > M} ∇f`. -/
theorem isWeakGrad_posPart_sub {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    (M : ℝ) : IsWeakGrad (fun y => max (f y - M) 0) (fun y k => if M < f y then g y k else 0) := by
  have h1 := isWeakGrad_max_zero_aux (h.sub_const M) (hf.sub (integrable_const M)) hg 1 (Or.inl rfl)
  convert h1 using 1
  funext y k
  by_cases h0 : M < f y
  · simp [h0, sub_pos.mpr h0]
  · have : ¬ 0 < f y - M := by linarith
    simp only [h0, this, ↓reduceIte]
    split_ifs <;> norm_num

/-- `∇ min(f, M) = 1_{f ≤ M} ∇f`. -/
theorem isWeakGrad_min {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    (M : ℝ) : IsWeakGrad (fun y => min (f y) M) (fun y k => if M < f y then 0 else g y k) := by
  have h1 := h.add ((isWeakGrad_posPart_sub h hf hg M).cmul (-1))
  convert h1 using 1
  · funext y
    rcases le_total (f y) M with hy | hy
    · rw [min_eq_left hy, max_eq_right (by linarith)]; ring
    · rw [min_eq_right hy, max_eq_left (by linarith)]; ring
  · funext y k
    split_ifs <;> ring

/-- `∇|f| = sign(f) ∇f`. -/
theorem isWeakGrad_abs {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume) :
    IsWeakGrad (fun y => |f y|)
      (fun y k => if 0 < f y then g y k else if f y < 0 then -g y k else 0) := by
  have hp := isWeakGrad_posPart_sub h hf hg 0
  have hn := isWeakGrad_posPart_sub (h.cmul (-1)) (hf.const_mul (-1))
    (fun k => (hg k).const_mul (-1)) 0
  have h1 := hp.add hn
  convert h1 using 1
  · funext y
    rcases le_total 0 (f y) with hy | hy
    · rw [abs_of_nonneg hy, sub_zero, sub_zero, max_eq_left hy, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos hy, sub_zero, sub_zero, max_eq_right hy, max_eq_left (by linarith)]
      ring
  · funext y k
    by_cases h1 : 0 < f y
    · have : ¬ (0 < -1 * f y) := by linarith
      have h3 : ¬ f y < 0 := by linarith
      simp [h1, this, h3]
    · by_cases h2 : f y < 0
      · have : 0 < -1 * f y := by linarith
        simp [h1, h2, this]
      · have : ¬ (0 < -1 * f y) := by linarith
        simp [h1, h2, this]

end SharpLSI
