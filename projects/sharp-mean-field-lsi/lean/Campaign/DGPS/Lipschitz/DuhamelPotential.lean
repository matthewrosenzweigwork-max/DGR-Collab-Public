import DGPS.Lipschitz.DuhamelOperator
import DGPS.Basic.ParabolicChainRuleTime

open MeasureTheory Set
open scoped Real RealInnerProductSpace
namespace DGPS.Lipschitz
open DGPS.Lipschitz.ParabolicChainRule
variable {d : ℕ}

/-- The Euclidean heat kernel, extended by `0` for non-positive times (measurable version of `Kh`). -/
noncomputable def Kt (τ : ℝ) (z : Tangent d) : ℝ :=
  ∑' n : Fin d → ℤ, if 0 < τ then gE τ (z + nE n) else 0

theorem summable_gE_shift {τ : ℝ} (hτ : 0 < τ) (z : Tangent d) :
    Summable fun n : Fin d → ℤ => gE τ (z + nE n) := by
  obtain ⟨B, hB0, hB⟩ := gE_shift_le (d := d) hτ ‖z‖
  exact Summable.of_nonneg_of_le (fun n => (gE_pos hτ _).le) (fun n => hB z (nE n) le_rfl)
    ((summable_gE_nE (d := d) (s := 2 * τ) (by positivity)).mul_left B)

theorem measurable_Kt : Measurable (fun p : ℝ × Tangent d => Kt p.1 p.2) := by
  unfold Kt
  refine measurable_tsum_real (fun n => ?_) (fun p => ?_)
  · refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
    exact measurable_gE2.comp (measurable_fst.prodMk (measurable_snd.add_const _))
  · by_cases hτ : 0 < p.1
    · simpa [hτ] using summable_gE_shift hτ p.2
    · simp [hτ]

theorem Kt_eq {τ : ℝ} (hτ : 0 < τ) (z : Tangent d) : Kt τ z = Kh τ z := by
  rw [Kh_eq_tsum hτ]
  simp [Kt, hτ]

theorem heatOp_eq_integral {τ : ℝ} (g : Torus d → ℝ) (x : Torus d) :
    heatOp τ g x = ∫ w, g w * Kh τ (secE x - secE w) ∂haar d := by
  rw [← Hl_eq]
  unfold Hl
  show heatOp τ g x = heatOp τ g (SharpLSI.liftT (SharpLSI.secT x))
  rw [SharpLSI.liftT_secT]

/-- Slice of the drift term. -/
noncomputable def gSlice (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d) (s : ℝ)
    (w : Torus d) : ℝ := ⟪b w, v (s, w)⟫

noncomputable def Iint0 (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d)
    (q : ((ℝ × Torus d) × ℝ) × Torus d) : ℝ :=
  ⟪b q.2, v (q.1.2, q.2)⟫ * Kt (q.1.1.1 - q.1.2) (secE q.1.1.2 - secE q.2)

theorem measurable_Iint0 {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) (hv : Measurable v) : Measurable (Iint0 b v) := by
  unfold Iint0
  refine Measurable.mul ?_ ?_
  · exact (hb.comp measurable_snd).inner
      (hv.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  · refine measurable_Kt.comp (Measurable.prodMk ?_ ?_)
    · exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst)
    · exact (measurable_secE.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).sub
        (measurable_secE.comp measurable_snd)

noncomputable def Jint0 (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d)
    (r : (ℝ × Torus d) × ℝ) : ℝ := ∫ w, Iint0 b v (r, w) ∂haar d

theorem stronglyMeasurable_Jint0 {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) (hv : Measurable v) : StronglyMeasurable (Jint0 b v) :=
  (measurable_Iint0 hb hv).stronglyMeasurable.integral_prod_right'

theorem Jint0_eq (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d) (p : ℝ × Torus d)
    {s : ℝ} (hs : 0 < p.1 - s) :
    Jint0 b v (p, s) = heatOp (p.1 - s) (gSlice b v s) p.2 := by
  rw [heatOp_eq_integral]
  unfold Jint0 Iint0 gSlice
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Kt_eq hs]

/-! ### Slice integration by parts -/

theorem kerGrad_apply {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} (hg : Integrable g (haar d))
    (x : Torus d) (j : Fin d) :
    kerGrad τ g x j = ∫ w, g w * lip026b_kern τ j x w ∂haar d := by
  have hi2 := integrable_smul_dKh hτ hg (secE x)
  have h : ⟪kerGrad τ g x, (EuclideanSpace.single j (1 : ℝ) : Tangent d)⟫ =
      ∫ w, g w * lip026b_kern τ j x w ∂haar d := by
    rw [← InnerProductSpace.toDual_apply_apply, toDual_kerGrad hτ hg x,
      ContinuousLinearMap.integral_apply hi2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp [lip026b_kern]
  rw [← h, EuclideanSpace.inner_single_right]
  simp

theorem slice_ibp {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} (hg : Integrable g (haar d))
    {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, heatOp τ g x * coordPartial j φ x ∂haar d = -∫ x, kerGrad τ g x j * φ x ∂haar d := by
  rw [integral_mul_coordPartial_of_c1 (isC1Periodic_heatOp hτ hg) hφ j]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [lip026b_coordPartial_heatOp hτ hg j x, kerGrad_apply hτ hg x j]

theorem abs_heatOp_le {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (x : Torus d) : |heatOp τ g x| ≤ M :=
  abs_torusConv_le (continuous_heatKernelT hτ) (fun z => (heatKernelT_pos hτ z).le)
    (integral_heatKernelT hτ) hM x

theorem abs_gSlice_le {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d} {B0 V : ℝ}
    (hbB : ∀ x, ‖b x‖ ≤ B0) (hvV : ∀ p, ‖v p‖ ≤ V) (s : ℝ) (w : Torus d) :
    |gSlice b v s w| ≤ B0 * V := by
  unfold gSlice
  calc |⟪b w, v (s, w)⟫| ≤ ‖b w‖ * ‖v (s, w)‖ := abs_real_inner_le_norm _ _
    _ ≤ B0 * V := mul_le_mul (hbB w) (hvV _) (norm_nonneg _) ((norm_nonneg _).trans (hbB w))

theorem measurable_gSlice {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) (hv : Measurable v) (s : ℝ) : Measurable (gSlice b v s) :=
  hb.inner (hv.comp (measurable_const.prodMk measurable_id))

theorem integrable_gSlice {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d} {B0 V : ℝ}
    (hb : Measurable b) (hv : Measurable v) (hbB : ∀ x, ‖b x‖ ≤ B0) (hvV : ∀ p, ‖v p‖ ≤ V)
    (s : ℝ) : Integrable (gSlice b v s) (haar d) :=
  Integrable.of_bound (measurable_gSlice hb hv s).aestronglyMeasurable (B0 * V)
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact abs_gSlice_le hbB hvV s w)

theorem abs_Jint0_le {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d} {B0 V : ℝ}
    (hbB : ∀ x, ‖b x‖ ≤ B0) (hvV : ∀ p, ‖v p‖ ≤ V) (r : (ℝ × Torus d) × ℝ) :
    |Jint0 b v r| ≤ B0 * V := by
  obtain ⟨p, s⟩ := r
  by_cases hs : 0 < p.1 - s
  · rw [Jint0_eq b v p hs]
    exact abs_heatOp_le hs (abs_gSlice_le hbB hvV s) _
  · have h0 : Jint0 b v (p, s) = 0 := by
      simp [Jint0, Iint0, Kt, hs]
    rw [h0, abs_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hbB 0)) ((norm_nonneg _).trans (hvV 0))

theorem norm_Jint_le {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d} {B0 V : ℝ}
    (hb : Measurable b) (hv : Measurable v) (hbB : ∀ x, ‖b x‖ ≤ B0) (hvV : ∀ p, ‖v p‖ ≤ V)
    {t s : ℝ} (hs : s ∈ Ioo 0 t) (x : Torus d) :
    ‖Jint b v ((t, x), s)‖ ≤ (π * (t - s)) ^ (-(1 : ℝ) / 2) * (B0 * V) := by
  rw [Jint_eq]
  exact norm_kerGrad_inner_le (by linarith [hs.2]) hb hbB
    (hv.comp (measurable_const.prodMk measurable_id)) (Filter.Eventually.of_forall fun w => hvV _) x

/-- The Duhamel potential `u(t) = H_t f + ∫₀ᵗ H_{t-s}(b · v(s)) ds`. -/
noncomputable def duhamelPotential (b : Torus d → Tangent d) (f : Torus d → ℝ)
    (v : ℝ × Torus d → Tangent d) (t : ℝ) (x : Torus d) : ℝ :=
  heatOp t f x + ∫ s in Ioo 0 t, heatOp (t - s) (gSlice b v s) x

theorem duhamelPotential_eq (b : Torus d → Tangent d) (f : Torus d → ℝ)
    (v : ℝ × Torus d → Tangent d) {t : ℝ} (x : Torus d) :
    duhamelPotential b f v t x = heatOp t f x + ∫ s in Ioo 0 t, Jint0 b v ((t, x), s) := by
  unfold duhamelPotential
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  exact (Jint0_eq b v (t, x) (by show 0 < t - s; linarith [hs.2])).symm

/-! ### The weak gradient of the Duhamel potential -/

theorem weakGradient_duhamelPotential {T B0 V : ℝ} {b : Torus d → Tangent d}
    (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hfc : Continuous f)
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V)
    (hfix : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b (heatGrad f) v p = v p)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x)) := by
  have ht0 : 0 < t := ht.1
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hvV 0)
  have hfi : Integrable f (haar d) := integrable_of_continuous_torus hfc
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) t) with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hcont : Continuous (heatOp t f) := (isC1Periodic_heatOp ht0 hfi).continuous_torus
  have hJ0m : StronglyMeasurable fun z : Torus d × ℝ => Jint0 b v ((t, z.1), z.2) :=
    (stronglyMeasurable_Jint0 hb hv).comp_measurable
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hJ0m' : StronglyMeasurable fun z : ℝ × Torus d => Jint0 b v ((t, z.2), z.1) :=
    (stronglyMeasurable_Jint0 hb hv).comp_measurable
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hUm : StronglyMeasurable fun x : Torus d => ∫ s, Jint0 b v ((t, x), s) ∂μ :=
    hJ0m.integral_prod_right' (ν := μ)
  have hUb : ∀ x, ‖∫ s, Jint0 b v ((t, x), s) ∂μ‖ ≤ B0 * V * t := by
    intro x
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) t)
      (f := fun s => Jint0 b v ((t, x), s)) (C := B0 * V) (by simp)
      (fun s _ => by rw [Real.norm_eq_abs]; exact abs_Jint0_le hbB hvV _)
    have hr : (volume : Measure ℝ).real (Ioo (0 : ℝ) t) = t := by
      simp [Measure.real, Real.volume_Ioo, ht0.le]
    rw [hr] at h
    exact h
  have hu : duhamelPotential b f v t = fun x => heatOp t f x + ∫ s, Jint0 b v ((t, x), s) ∂μ :=
    funext fun x => duhamelPotential_eq b f v x
  refine ⟨?_, ?_, ?_⟩
  · rw [hu]
    obtain ⟨Mf, -, hMf⟩ := exists_abs_le_of_continuous' hcont
    refine MemLp.of_bound (hcont.aestronglyMeasurable.add hUm.aestronglyMeasurable)
      (Mf + B0 * V * t) (Filter.Eventually.of_forall fun x => ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ (hUb x))
    simpa [Real.norm_eq_abs] using hMf x
  · exact MemLp.of_bound (hv.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable V
      (Filter.Eventually.of_forall fun x => hvV _)
  · intro φ hφ j
    have hAc : Continuous (coordPartial j φ) := hφ.continuous_coordPartial j
    have hφc : Continuous φ := hφ.continuous_torus
    obtain ⟨CA, -, hCA⟩ := exists_abs_le_of_continuous' hAc
    obtain ⟨Cφ, -, hCφ⟩ := exists_abs_le_of_continuous' hφc
    -- joint integrability of the first Fubini integrand
    have hF0 : Integrable (fun z : ℝ × Torus d => Jint0 b v ((t, z.2), z.1) * coordPartial j φ z.2)
        (μ.prod (haar d)) := by
      refine Integrable.of_bound ?_ (B0 * V * CA) (Filter.Eventually.of_forall fun z => ?_)
      · exact (hJ0m'.mul (hAc.comp continuous_snd).stronglyMeasurable).aestronglyMeasurable
      · show ‖Jint0 b v ((t, z.2), z.1) * coordPartial j φ z.2‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_Jint0_le hbB hvV _) (hCA _) (abs_nonneg _) (mul_nonneg hB0 hV0)
    -- the second Fubini integrand
    have hJ := (stronglyMeasurable_Jint hb hv).comp_measurable
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst :
        Measurable fun z : ℝ × Torus d => ((t, z.2), z.1))
    have hJj : StronglyMeasurable fun z : ℝ × Torus d => (Jint b v ((t, z.2), z.1)) j :=
      (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.comp_stronglyMeasurable hJ
    have hGmeas : Measurable fun z : ℝ × Torus d => (Jint b v ((t, z.2), z.1)) j * φ z.2 :=
      hJj.measurable.mul (hφc.comp continuous_snd).measurable
    have hbnd : Integrable (fun s : ℝ => π ^ (-(1 : ℝ) / 2) * (t - s) ^ (-(1 : ℝ) / 2) * (B0 * V)) μ :=
      ((integrableOn_sing ht0).const_mul _).mul_const _
    have hbndm : Measurable fun z : ℝ × Torus d =>
        π ^ (-(1 : ℝ) / 2) * (t - z.1) ^ (-(1 : ℝ) / 2) * (B0 * V) * Cφ := by fun_prop
    have hG : Integrable (fun z : ℝ × Torus d => (Jint b v ((t, z.2), z.1)) j * φ z.2)
        (μ.prod (haar d)) := by
      refine Integrable.mono' ((hbnd.mul_prod (integrable_const Cφ)) :
        Integrable (fun z : ℝ × Torus d =>
          π ^ (-(1 : ℝ) / 2) * (t - z.1) ^ (-(1 : ℝ) / 2) * (B0 * V) * Cφ) (μ.prod (haar d)))
        hGmeas.aestronglyMeasurable ?_
      refine (Measure.ae_prod_iff_ae_ae (measurableSet_le hGmeas.norm hbndm)).2 ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => ?_)
      refine Filter.Eventually.of_forall fun x => ?_
      show ‖(Jint b v ((t, x), s)) j * φ x‖ ≤ _
      have h1 : ‖(Jint b v ((t, x), s)) j‖ ≤ ‖Jint b v ((t, x), s)‖ := PiLp.norm_apply_le _ j
      have h2 := norm_Jint_le hb hv hbB hvV hs x
      rw [rpow_pi_mul (by linarith [hs.2])] at h2
      have h3 : ‖φ x‖ ≤ Cφ := by simpa [Real.norm_eq_abs] using hCφ x
      rw [norm_mul]
      exact mul_le_mul (h1.trans h2) h3 (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [hs.2]) _))
          (mul_nonneg hB0 hV0))
    -- slice identity
    have hstep : ∀ s ∈ Ioo (0 : ℝ) t, ∫ x, Jint0 b v ((t, x), s) * coordPartial j φ x ∂haar d =
        -∫ x, (Jint b v ((t, x), s)) j * φ x ∂haar d := by
      intro s hs
      have hτ : 0 < t - s := by linarith [hs.2]
      have h := slice_ibp hτ (integrable_gSlice hb hv hbB hvV s) hφ j
      calc ∫ x, Jint0 b v ((t, x), s) * coordPartial j φ x ∂haar d
          = ∫ x, heatOp (t - s) (gSlice b v s) x * coordPartial j φ x ∂haar d :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by
              show Jint0 b v ((t, x), s) * _ = _
              rw [Jint0_eq b v (t, x) hτ])
        _ = -∫ x, kerGrad (t - s) (gSlice b v s) x j * φ x ∂haar d := h
        _ = _ := rfl
    have hF0i : Integrable (fun x => ∫ s, Jint0 b v ((t, x), s) * coordPartial j φ x ∂μ)
        (haar d) := hF0.integral_prod_right
    have hGi : Integrable (fun x => ∫ s, (Jint b v ((t, x), s)) j * φ x ∂μ) (haar d) :=
      hG.integral_prod_right
    have hswap1 := integral_integral_swap (μ := μ) (ν := haar d)
      (f := fun (s : ℝ) (x : Torus d) => Jint0 b v ((t, x), s) * coordPartial j φ x) hF0
    have hswap2 := integral_integral_swap (μ := μ) (ν := haar d)
      (f := fun (s : ℝ) (x : Torus d) => (Jint b v ((t, x), s)) j * φ x) hG
    have hkc : ∀ x, kerGrad t f x j = coordPartial j (heatOp t f) x := fun x => by
      rw [kerGrad_apply ht0 hfi, lip026b_coordPartial_heatOp ht0 hfi j x]
    have hkcc : Continuous fun x => kerGrad t f x j * φ x := by
      have := (isC1Periodic_heatOp ht0 hfi).continuous_coordPartial j
      simp_rw [hkc]
      exact this.mul hφc
    have hLHS : ∫ x, duhamelPotential b f v t x * coordPartial j φ x ∂haar d =
        -∫ x, kerGrad t f x j * φ x ∂haar d -
          ∫ x, ∫ s, (Jint b v ((t, x), s)) j * φ x ∂μ ∂haar d := by
      have hpt : ∀ x, duhamelPotential b f v t x * coordPartial j φ x =
          heatOp t f x * coordPartial j φ x +
            ∫ s, Jint0 b v ((t, x), s) * coordPartial j φ x ∂μ := by
        intro x
        rw [duhamelPotential_eq, add_mul, integral_mul_const]
      calc ∫ x, duhamelPotential b f v t x * coordPartial j φ x ∂haar d
          = ∫ x, (heatOp t f x * coordPartial j φ x +
              ∫ s, Jint0 b v ((t, x), s) * coordPartial j φ x ∂μ) ∂haar d :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = ∫ x, heatOp t f x * coordPartial j φ x ∂haar d +
              ∫ x, ∫ s, Jint0 b v ((t, x), s) * coordPartial j φ x ∂μ ∂haar d :=
            integral_add (integrable_of_continuous_torus (hcont.mul hAc)) hF0i
        _ = -∫ x, kerGrad t f x j * φ x ∂haar d +
              ∫ s, ∫ x, Jint0 b v ((t, x), s) * coordPartial j φ x ∂haar d ∂μ := by
            rw [slice_ibp ht0 hfi hφ j, hswap1]
        _ = -∫ x, kerGrad t f x j * φ x ∂haar d +
              ∫ s, -∫ x, (Jint b v ((t, x), s)) j * φ x ∂haar d ∂μ := by
            congr 1
            exact setIntegral_congr_fun measurableSet_Ioo hstep
        _ = _ := by
            rw [integral_neg, hswap2]; ring
    -- the right hand side
    have hvj : ∀ x, v (t, x) j = kerGrad t f x j + ∫ s, (Jint b v ((t, x), s)) j ∂μ := by
      intro x
      have hsm : AEStronglyMeasurable (fun s => Jint b v ((t, x), s)) μ :=
        ((stronglyMeasurable_Jint hb hv).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      have hbd : ∀ᵐ s ∂μ, ‖Jint b v ((t, x), s)‖ ≤ (π * (t - s)) ^ (-(1 : ℝ) / 2) * (B0 * V) :=
        (ae_restrict_iff' measurableSet_Ioo).2
          (Filter.Eventually.of_forall fun s hs => norm_Jint_le hb hv hbB hvV hs x)
      have hint := (time_integral_bound ht0 hsm hbd).1
      have h2 : (∫ s, Jint b v ((t, x), s) ∂μ) j = ∫ s, (Jint b v ((t, x), s)) j ∂μ := by
        have := (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integral_comp_comm hint
        exact this.symm
      rw [← h2]
      have h3 := congrArg (fun w : Tangent d => w j) (hfix (t, x) ht)
      simp only [duhamelOp] at h3
      rw [← h3]
      rfl
    have hRHS : ∫ x, v (t, x) j * φ x ∂haar d =
        ∫ x, kerGrad t f x j * φ x ∂haar d +
          ∫ x, ∫ s, (Jint b v ((t, x), s)) j * φ x ∂μ ∂haar d := by
      rw [← integral_add (integrable_of_continuous_torus hkcc) hGi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show v (t, x) j * φ x = _
      rw [hvj x, add_mul]
      simp only []
      rw [integral_mul_const]
    show ∫ x, duhamelPotential b f v t x * coordPartial j φ x ∂haar d =
      -∫ x, v (t, x) j * φ x ∂haar d
    rw [hLHS, hRHS]; ring

/-- **LIP007b.** Under the hypotheses of `lip007a_duhamel_fixed_point`, the measurable fixed point
`v` of the Duhamel map (with `‖v‖ ≤ 2L`, `Φ v = v` on `0 < t < T`, and a.e. uniqueness) is the weak
gradient of the Duhamel potential `u(t) = H_t f + ∫₀ᵗ H_{t-s}(b · v(s)) ds` for every `0 < t < T`:
`IsWeakGradient (u t) (v(t, ·))`. -/
theorem lip007b_mild_gradient {T B0 L : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    {b : Torus d → Tangent d} (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hTB : 16 * B0 ^ 2 * T ≤ π) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
      (∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b (heatGrad f) v p = v p) ∧
      (∀ u : ℝ × Torus d → Tangent d, Measurable u → (∃ Mu, ∀ᵐ q ∂stMeasure d T, ‖u q‖ ≤ Mu) →
        u =ᵐ[stMeasure d T] duhamelOp b (heatGrad f) u → u =ᵐ[stMeasure d T] v) ∧
      ∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x)) := by
  obtain ⟨v, hvm, hvb, hvf, huniq⟩ := (lip007a_duhamel_fixed_point hT hL hb hbB hTB hf).2.2
  exact ⟨v, hvm, hvb, hvf, huniq, fun t ht =>
    weakGradient_duhamelPotential hb hbB (continuous_of_torusLipschitz hL hf) hvm hvb hvf ht⟩

end DGPS.Lipschitz
