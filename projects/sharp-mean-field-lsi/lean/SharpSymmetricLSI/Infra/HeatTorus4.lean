import SharpSymmetricLSI.Infra.HeatTorus3

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 4): smoothing

`x ↦ ∫ f(z) K(x - s z) dμ(z)` is `C^∞` when `f ∈ L¹(μ)` and `K` is `C^∞` with bounded derivatives
(`contDiff_integral_mul_sub`). With `K = P_t` this shows that `e^{tΔ} f` is smooth for every
integrable `f` (`isSmoothT_heatT`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

set_option maxHeartbeats 800000 in
/-- **Smoothing by a kernel with bounded derivatives.** -/
theorem contDiff_integral_mul_sub {f : Z → ℝ} (hf : Integrable f μ) {s : Z → E}
    (hs : AEStronglyMeasurable s μ) {K : E → ℝ} (hK : ContDiff ℝ ∞ K)
    (hKb : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n K x‖ ≤ C) :
    ContDiff ℝ ∞ (fun x => ∫ z, f z * K (x - s z) ∂μ) := by
  choose C hC using hKb
  set q := ftaylorSeries ℝ K with hq
  have hqK : HasFTaylorSeriesUpTo ∞ K q := hK.ftaylorSeries
  have hqc : ∀ m, Continuous fun y => q y m := fun m => hqK.cont m (by exact_mod_cast le_top)
  have hqb : ∀ m y, ‖q y m‖ ≤ C m := fun m y => hC m y
  have hmeas : ∀ m x, AEStronglyMeasurable (fun z => f z • q (x - s z) m) μ := fun m x =>
    hf.aestronglyMeasurable.smul
      ((hqc m).comp_aestronglyMeasurable (aestronglyMeasurable_const.sub hs))
  have hint : ∀ m x, Integrable (fun z => f z • q (x - s z) m) μ := fun m x => by
    refine (hf.norm.mul_const (C m)).mono' (hmeas m x) (Eventually.of_forall fun z => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hqb m _) (norm_nonneg _)
  let p : E → FormalMultilinearSeries ℝ E ℝ := fun x m => ∫ z, f z • q (x - s z) m ∂μ
  refine HasFTaylorSeriesUpTo.contDiff (f' := p) ⟨fun x => ?_, fun m _ x => ?_, fun m _ => ?_⟩
  · -- zeroth term
    simp only [p]
    let e0 := (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearIsometry
    calc (∫ z, f z • q (x - s z) 0 ∂μ).curry0 = e0 (∫ z, f z • q (x - s z) 0 ∂μ) := rfl
      _ = ∫ z, e0 (f z • q (x - s z) 0) ∂μ := (LinearIsometry.integral_comp_comm _ _).symm
      _ = ∫ z, f z * K (x - s z) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        show e0 (f z • q (x - s z) 0) = f z * K (x - s z)
        rw [e0.map_smul, smul_eq_mul]
        congr 1
  · -- derivative
    have hcl : ∀ A : ContinuousMultilinearMap ℝ (fun _ : Fin m.succ => E) ℝ,
        A.curryLeft = continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin m.succ => E) ℝ A :=
      fun A => rfl
    have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
      (F := fun x z => f z • q (x - s z) m)
      (F' := fun x z => f z • (q (x - s z) m.succ).curryLeft)
      (bound := fun z => ‖f z‖ * C m.succ) (x₀ := x) (s := univ) univ_mem
      (Eventually.of_forall fun x => hmeas m x) (hint m x)
      (by
        have hL : Continuous fun A : ContinuousMultilinearMap ℝ (fun _ : Fin m.succ => E) ℝ =>
            A.curryLeft := by
          simp_rw [hcl]; exact LinearIsometryEquiv.continuous _
        exact (hf.aestronglyMeasurable.smul ((hL.comp (hqc m.succ)).comp_aestronglyMeasurable
          (aestronglyMeasurable_const.sub hs))))
      (Eventually.of_forall fun z y _ => by
        rw [norm_smul, ContinuousMultilinearMap.curryLeft_norm]
        exact mul_le_mul_of_nonneg_left (hqb _ _) (norm_nonneg _))
      (hf.norm.mul_const _)
      (Eventually.of_forall fun z y _ => by
        have h1 := hqK.fderiv m (by exact_mod_cast WithTop.coe_lt_top _) (y - s z)
        have h2 : HasFDerivAt (fun y => y - s z) (ContinuousLinearMap.id ℝ E) y :=
          (hasFDerivAt_id y).sub_const _
        have h3 : HasFDerivAt (fun x => f z • q (x - s z) m)
            (f z • ((q (y - s z) m.succ).curryLeft.comp (ContinuousLinearMap.id ℝ E))) y :=
          (h1.comp y h2).const_smul (f z)
        simpa using h3)
    convert hderiv using 1
    show (∫ z, f z • q (x - s z) m.succ ∂μ).curryLeft =
      ∫ z, f z • (q (x - s z) m.succ).curryLeft ∂μ
    ext v w
    rw [ContinuousLinearMap.integral_apply (by
      refine (hf.norm.mul_const (C m.succ)).mono' ?_ (Eventually.of_forall fun z => ?_)
      · have hL : Continuous fun A : ContinuousMultilinearMap ℝ (fun _ : Fin m.succ => E) ℝ =>
            A.curryLeft := by
          simp_rw [hcl]; exact LinearIsometryEquiv.continuous _
        exact (hf.aestronglyMeasurable.smul ((hL.comp (hqc m.succ)).comp_aestronglyMeasurable
          (aestronglyMeasurable_const.sub hs)))
      · rw [norm_smul, ContinuousMultilinearMap.curryLeft_norm]
        exact mul_le_mul_of_nonneg_left (hqb _ _) (norm_nonneg _))]
    rw [ContinuousMultilinearMap.integral_apply]
    · simp only [ContinuousMultilinearMap.curryLeft_apply, smul_apply]
      rw [ContinuousMultilinearMap.integral_apply (hint m.succ x)]
      rfl
    · refine Integrable.mono' ((hf.norm.mul_const (C m.succ)).mul_const ‖v‖) ?_ ?_
      · exact (ContinuousLinearMap.apply ℝ _ v).continuous.comp_aestronglyMeasurable
          (by
            have hL : Continuous fun A : ContinuousMultilinearMap ℝ (fun _ : Fin m.succ => E) ℝ =>
                A.curryLeft := by
              simp_rw [hcl]; exact LinearIsometryEquiv.continuous _
            exact (hf.aestronglyMeasurable.smul ((hL.comp (hqc m.succ)).comp_aestronglyMeasurable
              ((aestronglyMeasurable_const (b := x)).sub hs))))
      · refine Eventually.of_forall fun z => ?_
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_smul, ContinuousMultilinearMap.curryLeft_norm]
        gcongr
        exact hqb _ _
  · -- continuity
    refine continuous_of_dominated (bound := fun z => ‖f z‖ * C m) (fun x => hmeas m x)
      (fun x => Eventually.of_forall fun z => ?_) (hf.norm.mul_const _)
      (Eventually.of_forall fun z => ?_)
    · rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hqb _ _) (norm_nonneg _)
    · exact (continuous_const (y := f z)).smul
        ((hqc m).comp (continuous_id.sub (continuous_const (y := s z))))

end Generic

section Periodic

variable {ι : Type*} [Fintype ι]

/-- A smooth `ℤ^ι`-periodic function has bounded derivatives of every order. -/
theorem iteratedFDeriv_bdd_of_periodic {K : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K)
    (hper : ∀ x (m : ι → ℤ), K (x + intVec m) = K x) (n : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ n K x‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ n K) :=
    hK.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1)
    ).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  let m : ι → ℤ := fun i => ⌊x i⌋
  have hx : x = (fun i => Int.fract (x i)) + intVec m := by
    funext i; simp [intVec, m, Int.fract_add_floor]
  have hper' : (fun y => K (y + intVec m)) = K := funext fun y => hper y m
  have : iteratedFDeriv ℝ n K x = iteratedFDeriv ℝ n K (fun i => Int.fract (x i)) := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := K) n (intVec m)
      (fun i => Int.fract (x i))
    rw [hper', ← hx] at h
    exact h.symm
  rw [this]
  exact hC _ fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem heatPL_add_intVec' (t : ℝ) (x : ι → ℝ) (m : ι → ℤ) :
    heatPL t (x + intVec m) = heatPL t x := heatPL_add_intVec t x m

theorem heatT_comp_liftT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) (x : ι → ℝ) :
    heatT t f (liftT x) = ∫ z, f z * heatPL t (x - secT z) := by
  rw [heatT_eq' ht hf]
  congr 1; funext z
  rw [← heatP_liftT, liftT_sub, liftT_secT]

/-- **The heat flow is smoothing.** -/
theorem isSmoothT_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Integrable f) :
    IsSmoothT (heatT t f) := by
  have h : heatT t f ∘ liftT = fun x => ∫ z, f z * heatPL t (x - secT z) :=
    funext fun x => heatT_comp_liftT ht hf.aestronglyMeasurable x
  rw [IsSmoothT, h]
  exact contDiff_integral_mul_sub hf measurable_secT.aestronglyMeasurable (contDiff_heatPL ht)
    (iteratedFDeriv_bdd_of_periodic (contDiff_heatPL ht) (heatPL_add_intVec t))

end Periodic

end SharpLSI
