import SharpSymmetricLSI.Paper.Defective3

/-!
# R03 (Proposition 2.2), part 4: slices and marginals of weak-gradient pairs

On `𝕋^{α ⊕ β} ≅ 𝕋^α × 𝕋^β` (`join a b = Sum.elim a b`), for an `L¹` weak-gradient pair `(f, g)`:
* (`isWeakGrad_sliceSum`) for a.e. `b`, the slice `a ↦ f(join a b)` has the weak gradient
  `a ↦ g(join a b)_{inl k}`;
* (`isWeakGrad_marginal`) the marginal `a ↦ ∫ f(join a b) db` has the weak gradient
  `a ↦ ∫ g(join a b)_{inl k} db`.

Slices: mollify (`moll n`), slice the smooth approximants (classical chain rule), pass to the `L¹`
limit along a subsequence that converges for a.e. `b` (`isWeakGrad_of_tendsto`). Marginals: integrate
the slice identities in `b` (Fubini).
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

section slice
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `join a b = Sum.elim a b`. -/
def join {X : Type*} (a : α → X) (b : β → X) : α ⊕ β → X := Sum.elim a b

theorem measurePreserving_join :
    MeasurePreserving (fun p : UnitAddTorus α × UnitAddTorus β => join p.1 p.2)
      ((volume : Measure (UnitAddTorus α)).prod volume) volume := by
  have h := (measurePreserving_sumPiEquivProdPi
    (fun _ : α ⊕ β => (volume : Measure UnitAddCircle))).symm
  convert h using 1
  funext p
  simp [join, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
  rfl

theorem measurable_join : Measurable (fun p : UnitAddTorus α × UnitAddTorus β => join p.1 p.2) :=
  measurePreserving_join.measurable

theorem liftT_join (x : α → ℝ) (z : β → ℝ) : liftT (join x z) = join (liftT x) (liftT z) := by
  funext i; cases i <;> rfl

theorem secT_join (a : UnitAddTorus α) (b : UnitAddTorus β) :
    secT (join a b) = join (secT a) (secT b) := by
  funext i; cases i <;> rfl

/-- The linear part of `x ↦ join x z`. -/
noncomputable def joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ) :=
  ContinuousLinearMap.pi fun i => Sum.elim (fun a => ContinuousLinearMap.proj a) (fun _ => 0) i

theorem joinCLM_apply (x : α → ℝ) : (joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ)) x = join x 0 := by
  funext i; cases i <;> rfl

theorem join_eq_add (x : α → ℝ) (z : β → ℝ) :
    join x z = (joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ)) x + join 0 z := by
  rw [joinCLM_apply]; funext i; cases i <;> simp [join]

theorem joinCLM_single (k : α) :
    (joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ)) (Pi.single k 1) = Pi.single (Sum.inl k) 1 := by
  rw [joinCLM_apply]
  funext i
  cases i with
  | inl a =>
    by_cases h : a = k
    · subst h; simp [join]
    · simp [join, Pi.single_apply, h]
  | inr b => simp [join]

/-- Slices of smooth periodic functions: the classical gradient. -/
theorem isWeakGrad_slice_smooth {F : UnitAddTorus (α ⊕ β) → ℝ} (hF : ContDiff ℝ 1 (F ∘ liftT))
    (b : UnitAddTorus β) :
    IsWeakGrad (fun a => F (join a b))
      (fun a k => fderiv ℝ (F ∘ liftT) (secT (join a b)) (Pi.single (Sum.inl k) 1)) := by
  have hlift : (fun a => F (join a b)) ∘ liftT = fun x => (F ∘ liftT) (join x (secT b)) := by
    funext x; simp only [Function.comp_apply, liftT_join, liftT_secT]
  have hJ : ContDiff ℝ ∞ (fun x : α → ℝ => join x (secT b)) := by
    have : (fun x : α → ℝ => join x (secT b)) = fun x => joinCLM x + join 0 (secT b) := by
      funext x; exact join_eq_add x (secT b)
    rw [this]
    exact (joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ)).contDiff.add contDiff_const
  have hs : ContDiff ℝ 1 ((fun a => F (join a b)) ∘ liftT) := by
    rw [hlift]; exact hF.comp (hJ.of_le (by simp))
  convert isWeakGrad_of_contDiff hs using 1
  funext a k
  rw [hlift]
  have hd : HasFDerivAt (fun x : α → ℝ => join x (secT b))
      (joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ)) (secT a) := by
    have : (fun x : α → ℝ => join x (secT b)) = fun x => joinCLM x + join 0 (secT b) := by
      funext x; exact join_eq_add x (secT b)
    rw [this]
    exact (joinCLM : (α → ℝ) →L[ℝ] (α ⊕ β → ℝ)).hasFDerivAt.add_const _
  have hc := ((hF.differentiable (by norm_num)) (join (secT a) (secT b))).hasFDerivAt.comp (secT a) hd
  rw [show (fun x : α → ℝ => (F ∘ liftT) (join x (secT b))) =
    (F ∘ liftT) ∘ (fun x => join x (secT b)) from rfl, hc.fderiv, ContinuousLinearMap.comp_apply,
    joinCLM_single, secT_join]

/-- Integrability of slices along a.e. `b`. -/
theorem ae_integrable_slice {u : UnitAddTorus (α ⊕ β) → ℝ} (hu : Integrable u volume) :
    ∀ᵐ b ∂(volume : Measure (UnitAddTorus β)), Integrable (fun a => u (join a b)) volume := by
  have h := measurePreserving_join.integrable_comp_of_integrable hu
  exact h.prod_left_ae

theorem measurableEmbedding_join :
    MeasurableEmbedding (fun p : UnitAddTorus α × UnitAddTorus β => join p.1 p.2) := by
  have h := (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => UnitAddCircle)).symm.measurableEmbedding
  convert h using 1
  funext p
  simp [join, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
  rfl

/-- Iterated integrals over `𝕋^{α ⊕ β}`. -/
theorem lintegral_join {u : UnitAddTorus (α ⊕ β) → ℝ≥0∞} (hu : AEMeasurable u volume) :
    ∫⁻ y, u y = ∫⁻ b, ∫⁻ a, u (join a b) := by
  rw [← measurePreserving_join.lintegral_comp_emb measurableEmbedding_join]
  exact lintegral_prod_symm (fun z => u (join z.1 z.2))
    (hu.comp_quasiMeasurePreserving measurePreserving_join.quasiMeasurePreserving)

theorem aemeasurable_lintegral_slice {u : UnitAddTorus (α ⊕ β) → ℝ≥0∞} (hu : AEMeasurable u volume) :
    AEMeasurable (fun b : UnitAddTorus β => ∫⁻ a, u (join a b)) volume :=
  (hu.comp_quasiMeasurePreserving measurePreserving_join.quasiMeasurePreserving).lintegral_prod_left'

theorem integrable_moll' (n : ℕ) {ι : Type*} [Fintype ι] {u : UnitAddTorus ι → ℝ}
    (hu : Integrable u volume) : Integrable (moll n u) volume :=
  ⟨(measurable_moll n hu).aestronglyMeasurable, (lintegral_moll_le n hu).trans_lt hu.2⟩

/-- **Slices of weak-gradient pairs.** -/
theorem isWeakGrad_sliceSum {f : UnitAddTorus (α ⊕ β) → ℝ} {g : UnitAddTorus (α ⊕ β) → α ⊕ β → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume) :
    ∀ᵐ b ∂(volume : Measure (UnitAddTorus β)),
      IsWeakGrad (fun a => f (join a b)) (fun a k => g (join a b) (Sum.inl k)) := by
  -- smooth approximants
  set F : ℕ → UnitAddTorus (α ⊕ β) → ℝ := fun n => moll n f with hFdef
  set G : ℕ → UnitAddTorus (α ⊕ β) → α ⊕ β → ℝ := fun n y k => moll n (fun z => g z k) y
    with hGdef
  have hFs : ∀ n, ContDiff ℝ ∞ (F n ∘ liftT) := fun n => moll_comp_liftT_contDiff n hf
  have hFG : ∀ n y k, G n y k = fderiv ℝ (F n ∘ liftT) (secT y) (Pi.single k 1) := by
    intro n y k
    simp only [hFdef, hGdef]
    rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n (secT y) k]
    rfl
  have hFi : ∀ n, Integrable (F n) volume := fun n => integrable_moll' n hf
  have hGi : ∀ n k, Integrable (fun y => G n y k) volume := fun n k => integrable_moll' n (hg k)
  have hFt : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ) atTop (𝓝 0) := tendsto_moll hf
  have hGt : ∀ k, Tendsto (fun n => ∫⁻ y, ‖G n y k - g y k‖ₑ) atTop (𝓝 0) :=
    fun k => tendsto_moll (hg k)
  -- the fibrewise errors
  set Φ : ℕ → UnitAddTorus β → ℝ≥0∞ := fun n b =>
    (∫⁻ a, ‖F n (join a b) - f (join a b)‖ₑ) +
      ∑ k : α, ∫⁻ a, ‖G n (join a b) (Sum.inl k) - g (join a b) (Sum.inl k)‖ₑ with hΦdef
  have hAm : ∀ n, AEMeasurable (fun y => ‖F n y - f y‖ₑ) volume := fun n =>
    ((hFi n).sub hf).aestronglyMeasurable.enorm
  have hBm : ∀ n k, AEMeasurable (fun y => ‖G n y k - g y k‖ₑ) volume := fun n k =>
    ((hGi n k).sub (hg k)).aestronglyMeasurable.enorm
  have hΦm : ∀ n, AEMeasurable (Φ n) volume := fun n => by
    simp only [hΦdef]
    exact (aemeasurable_lintegral_slice (hAm n)).add
      (Finset.aemeasurable_fun_sum _ fun k _ => aemeasurable_lintegral_slice (hBm n (Sum.inl k)))
  have hΦint : ∀ n, ∫⁻ b, Φ n b = (∫⁻ y, ‖F n y - f y‖ₑ) +
      ∑ k : α, ∫⁻ y, ‖G n y (Sum.inl k) - g y (Sum.inl k)‖ₑ := by
    intro n
    simp only [hΦdef]
    rw [lintegral_add_left' (aemeasurable_lintegral_slice (hAm n)),
      lintegral_finset_sum' _ fun k _ => aemeasurable_lintegral_slice (hBm n (Sum.inl k)),
      ← lintegral_join (hAm n)]
    congr 1
    exact Finset.sum_congr rfl fun k _ => (lintegral_join (hBm n (Sum.inl k))).symm
  have hΦt : Tendsto (fun n => ∫⁻ b, Φ n b) atTop (𝓝 0) := by
    simp_rw [hΦint]
    have := hFt.add (tendsto_finset_sum (Finset.univ : Finset α) fun k _ => hGt (Sum.inl k))
    simpa using this
  -- an a.e. convergent subsequence
  have hfin : ∀ᵐ b ∂(volume : Measure (UnitAddTorus β)), ∀ n, Φ n b ≠ ⊤ := by
    rw [ae_all_iff]
    intro n
    refine (ae_lt_top' (hΦm n) ?_).mono fun b hb => hb.ne
    rw [hΦint]
    exact ENNReal.add_ne_top.mpr ⟨((hFi n).sub hf).2.ne,
      ENNReal.sum_ne_top.mpr fun k _ => ((hGi n (Sum.inl k)).sub (hg (Sum.inl k))).2.ne⟩
  obtain ⟨ns, -, hns⟩ := exists_subseq_ae_of_tendsto_lintegral (μ := (volume : Measure (UnitAddTorus β)))
    (F := fun n b => (Φ n b).toReal) (f := fun _ => 0)
    (fun n => (hΦm n).ennreal_toReal.aestronglyMeasurable) aestronglyMeasurable_const (by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΦt
        (fun _ => bot_le) fun n => ?_
      refine lintegral_mono fun b => ?_
      simp only [sub_zero, Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le)
  -- integrability of the slices
  have hsf := ae_integrable_slice hf
  have hsg : ∀ᵐ b ∂(volume : Measure (UnitAddTorus β)), ∀ k,
      Integrable (fun a => g (join a b) k) volume := ae_all_iff.mpr fun k => ae_integrable_slice (hg k)
  have hsF : ∀ᵐ b ∂(volume : Measure (UnitAddTorus β)), ∀ n,
      Integrable (fun a => F n (join a b)) volume := ae_all_iff.mpr fun n => ae_integrable_slice (hFi n)
  have hsG : ∀ᵐ b ∂(volume : Measure (UnitAddTorus β)), ∀ n k,
      Integrable (fun a => G n (join a b) k) volume :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun k => ae_integrable_slice (hGi n k)
  filter_upwards [hfin, hns, hsf, hsg, hsF, hsG] with b hb1 hb2 hb3 hb4 hb5 hb6
  have hΦ0 : Tendsto (fun m => Φ (ns m) b) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal hb2)
    rw [ENNReal.ofReal_zero] at this
    exact this.congr fun m => ENNReal.ofReal_toReal (hb1 _)
  refine isWeakGrad_of_tendsto (F := fun m a => F (ns m) (join a b))
    (G := fun m a k => G (ns m) (join a b) (Sum.inl k)) (fun m => ?_) (fun m => hb5 _)
    (fun m k => hb6 _ _) hb3 (fun k => hb4 _) ?_ (fun k => ?_)
  · convert isWeakGrad_slice_smooth ((hFs (ns m)).of_le (by simp)) b using 1
    funext a k
    rw [hFG]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΦ0
      (fun _ => bot_le) fun m => ?_
    simp only [hΦdef]
    exact le_self_add
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΦ0
      (fun _ => bot_le) fun m => ?_
    simp only [hΦdef]
    refine le_trans ?_ le_add_self
    exact Finset.single_le_sum (f := fun k : α => ∫⁻ a, ‖G (ns m) (join a b) (Sum.inl k) -
      g (join a b) (Sum.inl k)‖ₑ) (fun _ _ => bot_le) (Finset.mem_univ k)

theorem integrable_marginal {u : UnitAddTorus (α ⊕ β) → ℝ} (hu : Integrable u volume) :
    Integrable (fun a => ∫ b, u (join a b)) volume :=
  (measurePreserving_join.integrable_comp_of_integrable hu).integral_prod_left

/-- `(x, b) ↦ join (liftT x) b` is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_joinLift :
    Measure.QuasiMeasurePreserving (fun p : (α → ℝ) × UnitAddTorus β => join (liftT p.1) p.2)
      ((volume : Measure (α → ℝ)).prod volume) volume := by
  have hm : Measurable (fun p : (α → ℝ) × UnitAddTorus β => join (liftT p.1) p.2) :=
    measurable_join.comp ((measurable_liftT.comp measurable_fst).prodMk measurable_snd)
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hm hs)]
  have hjs : MeasurableSet ((fun p : UnitAddTorus α × UnitAddTorus β => join p.1 p.2) ⁻¹' s) :=
    measurable_join hs
  have hnull : ((volume : Measure (UnitAddTorus α)).prod volume)
      ((fun p : UnitAddTorus α × UnitAddTorus β => join p.1 p.2) ⁻¹' s) = 0 := by
    rw [measurePreserving_join.measure_preimage hs.nullMeasurableSet, h0]
  rw [Measure.prod_apply_symm hjs, lintegral_eq_zero_iff (measurable_measure_prodMk_right hjs)] at hnull
  refine lintegral_eq_zero_iff (measurable_measure_prodMk_right (hm hs)) |>.mpr ?_
  filter_upwards [hnull] with b hb
  simp only [Pi.zero_apply] at hb ⊢
  have := quasiMeasurePreserving_liftT.preimage_null (s := (fun a => (a, b)) ⁻¹'
    ((fun p : UnitAddTorus α × UnitAddTorus β => join p.1 p.2) ⁻¹' s)) hb
  exact this

theorem aestronglyMeasurable_joinLift {u : UnitAddTorus (α ⊕ β) → ℝ}
    (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun p : (α → ℝ) × UnitAddTorus β => u (join (liftT p.1) p.2))
      ((volume : Measure (α → ℝ)).prod volume) :=
  hu.comp_quasiMeasurePreserving quasiMeasurePreserving_joinLift

/-- Fubini for a lifted torus function against a compactly supported bounded weight. -/
theorem integrable_joinLift_mul {u : UnitAddTorus (α ⊕ β) → ℝ} (hu : Integrable u volume)
    {φ : (α → ℝ) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : (α → ℝ) × UnitAddTorus β => u (join (liftT p.1) p.2) * φ p.1)
      ((volume : Measure (α → ℝ)).prod volume) := by
  have hm : AEStronglyMeasurable (fun p : (α → ℝ) × UnitAddTorus β =>
      u (join (liftT p.1) p.2) * φ p.1) ((volume : Measure (α → ℝ)).prod volume) :=
    (aestronglyMeasurable_joinLift hu.aestronglyMeasurable).mul
      (hφ.comp continuous_fst).aestronglyMeasurable
  refine (integrable_prod_iff hm).mpr ⟨?_, ?_⟩
  · have h1 := (measurePreserving_join.integrable_comp_of_integrable hu).prod_right_ae
    filter_upwards [quasiMeasurePreserving_liftT.ae h1] with x hx
    exact hx.mul_const _
  · have hU := integrable_marginal hu.norm
    have hloc := locallyIntegrable_comp_liftT hU
    have := hloc.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, smul_eq_mul, norm_mul]
    rw [integral_mul_const]

/-- **Marginals of weak-gradient pairs.** -/
theorem isWeakGrad_marginal {f : UnitAddTorus (α ⊕ β) → ℝ} {g : UnitAddTorus (α ⊕ β) → α ⊕ β → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume) :
    IsWeakGrad (fun a => ∫ b, f (join a b)) (fun a k => ∫ b, g (join a b) (Sum.inl k)) := by
  refine ⟨locallyIntegrable_comp_liftT (integrable_marginal hf),
    fun k => locallyIntegrable_comp_liftT (integrable_marginal (hg (Sum.inl k))),
    fun φ hφ hφc k => ?_⟩
  have hdφ : Continuous fun x => fderiv ℝ φ x (Pi.single k 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport fun x => fderiv ℝ φ x (Pi.single k 1) :=
    hφc.fderiv_apply (𝕜 := ℝ) _
  have i1 := integrable_joinLift_mul hf hdφ hdφc
  have i2 := integrable_joinLift_mul (hg (Sum.inl k)) hφ.continuous hφc
  have hsl := isWeakGrad_sliceSum h hf hg
  calc ∫ x, (fun a => ∫ b, f (join a b)) (liftT x) * fderiv ℝ φ x (Pi.single k 1)
      = ∫ x, ∫ b, f (join (liftT x) b) * fderiv ℝ φ x (Pi.single k 1) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only; rw [integral_mul_const]
    _ = ∫ b, ∫ x, f (join (liftT x) b) * fderiv ℝ φ x (Pi.single k 1) :=
        integral_integral_swap i1
    _ = ∫ b, -∫ x, g (join (liftT x) b) (Sum.inl k) * φ x := by
        refine integral_congr_ae ?_
        filter_upwards [hsl] with b hb
        exact hb.ibp φ hφ hφc k
    _ = -∫ x, ∫ b, g (join (liftT x) b) (Sum.inl k) * φ x := by
        rw [integral_neg]
        congr 1
        exact (integral_integral_swap i2).symm
    _ = -∫ x, (fun a k => ∫ b, g (join a b) (Sum.inl k)) (liftT x) k * φ x := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only; rw [integral_mul_const]

end slice


end SharpLSI
