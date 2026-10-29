import DGPS.Basic.HeatKernelBounds

/-!
# The `L^∞` space-time Duhamel operator (LIP007a)

For a bounded measurable drift `b` on `𝕋^d` and a Lipschitz `f`, the Duhamel map
`Φ v (t,x) = ∇H_t f (x) + ∫₀ᵗ ∇H_{t-s}(b · v(s)) (x) ds` is shown to be jointly measurable and
independent of the representative of `v` (a.e. for `Leb|(0,T) ⊗ haar`), a contraction in the
sup norm with constant `2 B0 √(T/π)` (from the `(π t)^{-1/2}` bound on `∇H_t`), and, for
`16 B0² T ≤ π`, to have a unique fixed point.  The fixed point is built by Picard iteration in the
sup norm on the slab `0 < t < T`.
Main export: `DGPS.Lipschitz.lip007a_duhamel_fixed_point`.
-/
open MeasureTheory Set
open scoped Real RealInnerProductSpace
namespace DGPS.Lipschitz
variable {d : ℕ}


theorem measurable_tsum_real {ι α : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace α] {f : ι → α → ℝ} (h : ∀ i, Measurable (f i))
    (hs : ∀ a, Summable fun i => f i a) : Measurable fun a => ∑' i, f i a := by
  have hm : Measurable (fun p : α × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left (fun i => h i)
  have key : (fun a => ∑' i, f i a) = fun a => ∫ i, f i a ∂(Measure.count : Measure ι) := by
    funext a
    have hint : Integrable (fun i => f i a) (Measure.count : Measure ι) := by
      rw [integrable_count_iff]
      exact (hs a).abs
    rw [integral_countable hint]
    refine tsum_congr fun i => ?_
    simp
  rw [key]
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_gE2 : Measurable (fun p : ℝ × Tangent d => gE p.1 p.2) := by
  unfold gE
  fun_prop

noncomputable def Dk (τ : ℝ) (z : Tangent d) : Tangent d :=
  WithLp.toLp 2 fun j => ∑' n : Fin d → ℤ,
    if 0 < τ then -(gE τ (z + nE n) / (2 * τ)) * (z + nE n) j else 0

theorem summable_Dk_coord (τ : ℝ) (z : Tangent d) (j : Fin d) :
    Summable fun n : Fin d → ℤ =>
      if 0 < τ then -(gE τ (z + nE n) / (2 * τ)) * (z + nE n) j else 0 := by
  by_cases hτ : 0 < τ
  · simp only [hτ, ite_true]
    refine Summable.of_norm_bounded (summable_norm_dterm hτ z) fun n => ?_
    rw [norm_smul, innerSL_apply_norm, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa using (PiLp.norm_apply_le (z + nE n) j)
  · simp [hτ]

theorem measurable_Dk : Measurable (fun p : ℝ × Tangent d => Dk p.1 p.2) := by
  unfold Dk
  refine (WithLp.measurable_toLp 2 _).comp ?_
  refine Measurable.of_eval fun j => ?_
  refine measurable_tsum_real (fun n => ?_) (fun p => summable_Dk_coord p.1 p.2 j)
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  have hg : Measurable fun p : ℝ × Tangent d => gE p.1 (p.2 + nE n) :=
    measurable_gE2.comp (measurable_fst.prodMk (measurable_snd.add_const _))
  have hz : Measurable fun p : ℝ × Tangent d => (p.2 + nE n) j :=
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)).comp (measurable_snd.add_const _)
  exact ((hg.div (measurable_fst.const_mul 2)).neg).mul hz

theorem Dk_eq {τ : ℝ} (hτ : 0 < τ) (z : Tangent d) :
    Dk τ z = (InnerProductSpace.toDual ℝ (Tangent d)).symm (fderiv ℝ (Kh τ) z) := by
  rw [LinearIsometryEquiv.eq_symm_apply]
  ext a
  rw [(hasFDerivAt_Kh hτ z).fderiv]
  have hsum := summable_norm_dterm hτ z
  have e1 := (ContinuousLinearMap.apply ℝ ℝ a).map_tsum hsum.of_norm
  simp only [ContinuousLinearMap.apply_apply] at e1
  rw [e1, InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
  simp only [Dk, ite_true, hτ]
  have hs : ∀ x : Fin d, Summable fun n : Fin d → ℤ =>
      -(gE τ (z + nE n) / (2 * τ)) * (z + nE n).ofLp x := fun x => by
    simpa [hτ] using summable_Dk_coord τ z x
  calc _ = ∑ x : Fin d, ∑' n : Fin d → ℤ,
        a.ofLp x * (-(gE τ (z + nE n) / (2 * τ)) * (z + nE n).ofLp x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [RCLike.inner_apply, conj_trivial]
        rw [← tsum_mul_left]
    _ = ∑' n : Fin d → ℤ, ∑ x : Fin d,
        a.ofLp x * (-(gE τ (z + nE n) / (2 * τ)) * (z + nE n).ofLp x) :=
        (Summable.tsum_finsetSum (fun x _ => (hs x).mul_left _)).symm
    _ = _ := by
        refine tsum_congr fun n => ?_
        simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, PiLp.inner_apply,
          RCLike.inner_apply, conj_trivial, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring

/-- Gradient of the heat kernel integral on the torus, written with the explicit Riesz vector. -/
noncomputable def kerGrad (τ : ℝ) (g : Torus d → ℝ) (x : Torus d) : Tangent d :=
  ∫ w, g w • Dk τ (secE x - secE w) ∂haar d

theorem norm_Dk_eq {τ : ℝ} (hτ : 0 < τ) (z : Tangent d) : ‖Dk τ z‖ = ‖fderiv ℝ (Kh τ) z‖ := by
  rw [Dk_eq hτ z]; exact LinearIsometryEquiv.norm_map _ _

theorem aesm_kerGrad_integrand (τ : ℝ) {g : Torus d → ℝ} (hg : AEStronglyMeasurable g (haar d))
    (x : Torus d) :
    AEStronglyMeasurable (fun w => g w • Dk τ (secE x - secE w)) (haar d) := by
  refine hg.smul ?_
  exact (measurable_Dk.comp (measurable_const.prodMk
    (measurable_const.sub measurable_secE))).aestronglyMeasurable

theorem integrable_kerGrad_integrand {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ}
    (hg : Integrable g (haar d)) (x : Torus d) :
    Integrable (fun w => g w • Dk τ (secE x - secE w)) (haar d) := by
  obtain ⟨M0, hM0, hb⟩ := exists_bound_dKh hτ (secE x)
  refine Integrable.mono' (hg.norm.mul_const M0) (aesm_kerGrad_integrand τ hg.aestronglyMeasurable x)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_smul, norm_Dk_eq hτ]
  exact mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _)

theorem toDual_kerGrad {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} (hg : Integrable g (haar d))
    (x : Torus d) :
    InnerProductSpace.toDual ℝ (Tangent d) (kerGrad τ g x) =
      ∫ w, g w • fderiv ℝ (Kh τ) (secE x - secE w) ∂haar d := by
  ext a
  rw [InnerProductSpace.toDual_apply_apply]
  have hi := integrable_kerGrad_integrand hτ hg x
  have hi2 := integrable_smul_dKh hτ hg (secE x)
  rw [ContinuousLinearMap.integral_apply hi2, kerGrad, real_inner_comm, ← integral_inner hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_apply, real_inner_smul_right, smul_eq_mul]
  rw [Dk_eq hτ, real_inner_comm, InnerProductSpace.toDual_apply_apply.symm,
    LinearIsometryEquiv.apply_symm_apply]

theorem norm_kerGrad {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} (hg : Integrable g (haar d))
    (x : Torus d) :
    ‖kerGrad τ g x‖ = ‖fderiv ℝ (Hl τ g) (secE x)‖ := by
  rw [← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ (Tangent d)), toDual_kerGrad hτ hg,
    (hasFDerivAt_Hl hτ hg (secE x)).fderiv]

theorem norm_kerGrad_le {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g (haar d)) (hM : ∀ᵐ w ∂haar d, |g w| ≤ M) (x : Torus d) :
    ‖kerGrad τ g x‖ ≤ (π * τ) ^ (-(1 : ℝ) / 2) * M := by
  have hgi : Integrable g (haar d) := Integrable.of_bound hg M (hM.mono fun w hw => by
    rwa [Real.norm_eq_abs])
  rw [norm_kerGrad hτ hgi]
  exact ((periodized_heat_gradient_bounds hτ).1 hg hM (secE x)).2

theorem kerGrad_sub {τ : ℝ} (hτ : 0 < τ) {g₁ g₂ : Torus d → ℝ} (h₁ : Integrable g₁ (haar d))
    (h₂ : Integrable g₂ (haar d)) (x : Torus d) :
    kerGrad τ (fun w => g₁ w - g₂ w) x = kerGrad τ g₁ x - kerGrad τ g₂ x := by
  unfold kerGrad
  rw [← integral_sub (integrable_kerGrad_integrand hτ h₁ x) (integrable_kerGrad_integrand hτ h₂ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [sub_smul]

/-- The Duhamel map `Φ(v)(t,x) = F(t,x) + ∫₀ᵗ ∇H_{t-s}(b·v(s)) (x) ds`. -/
noncomputable def duhamelOp (b : Torus d → Tangent d) (F v : ℝ × Torus d → Tangent d)
    (p : ℝ × Torus d) : Tangent d :=
  F p + ∫ s in Ioo 0 p.1, kerGrad (p.1 - s) (fun w => ⟪b w, v (s, w)⟫) p.2

/-- The integrand of the space-time Duhamel kernel integral, as a function of `((p, s), w)`. -/
noncomputable def Iint (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d)
    (q : ((ℝ × Torus d) × ℝ) × Torus d) : Tangent d :=
  ⟪b q.2, v (q.1.2, q.2)⟫ • Dk (q.1.1.1 - q.1.2) (secE q.1.1.2 - secE q.2)

theorem measurable_Iint {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) (hv : Measurable v) : Measurable (Iint b v) := by
  unfold Iint
  refine Measurable.smul
    (f := fun q : ((ℝ × Torus d) × ℝ) × Torus d => ⟪b q.2, v (q.1.2, q.2)⟫)
    (g := fun q : ((ℝ × Torus d) × ℝ) × Torus d =>
      Dk (q.1.1.1 - q.1.2) (secE q.1.1.2 - secE q.2)) ?_ ?_
  · exact (hb.comp measurable_snd).inner (hv.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  · refine measurable_Dk.comp (Measurable.prodMk ?_ ?_)
    · exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst)
    · exact (measurable_secE.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).sub
        (measurable_secE.comp measurable_snd)

/-- The inner (spatial) integral `∫ w, Iint ((p,s),w)`, i.e. `∇H_{t-s}(b·v(s))(x)`. -/
noncomputable def Jint (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d)
    (r : (ℝ × Torus d) × ℝ) : Tangent d :=
  ∫ w, Iint b v (r, w) ∂haar d

theorem Jint_eq (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d) (p : ℝ × Torus d) (s : ℝ) :
    Jint b v (p, s) = kerGrad (p.1 - s) (fun w => ⟪b w, v (s, w)⟫) p.2 := rfl

theorem stronglyMeasurable_Jint {b : Torus d → Tangent d} {v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) (hv : Measurable v) : StronglyMeasurable (Jint b v) :=
  (measurable_Iint hb hv).stronglyMeasurable.integral_prod_right'

theorem measurable_duhamelOp {b : Torus d → Tangent d} {F v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) (hF : Measurable F) (hv : Measurable v) :
    Measurable (duhamelOp b F v) := by
  have hJ := stronglyMeasurable_Jint hb hv
  let G : (ℝ × Torus d) × ℝ → Tangent d := fun r => if r.2 ∈ Ioo 0 r.1.1 then Jint b v r else 0
  have hset : MeasurableSet {r : (ℝ × Torus d) × ℝ | r.2 ∈ Ioo 0 r.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.comp measurable_fst))
  have hG : StronglyMeasurable G := by
    refine (hJ.measurable.ite hset measurable_const).stronglyMeasurable
  have hK := hG.integral_prod_right' (ν := (volume : Measure ℝ))
  have : duhamelOp b F v = fun p => F p + ∫ s, G (p, s) := by
    funext p
    unfold duhamelOp
    congr 1
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ Ioo 0 p.1
    · rw [Set.indicator_of_mem hs]
      simp only [G, hs, ↓reduceIte, Jint_eq]
    · rw [Set.indicator_of_notMem hs]
      simp only [G, hs, ↓reduceIte]
  rw [this]
  exact hF.add hK.measurable

/-- The space-time reference measure on `(0,T) × 𝕋^d`. -/
noncomputable def stMeasure (d : ℕ) (T : ℝ) : Measure (ℝ × Torus d) :=
  (volume.restrict (Ioo 0 T)).prod (haar d)

/-- Representative independence: `Φ(v)(p)` only depends on the `ν_T`-class of `v`, at every point
`p = (t, x)` with `t ≤ T` (no measurability needed). -/
theorem duhamelOp_congr {T : ℝ} {b : Torus d → Tangent d} {F v v' : ℝ × Torus d → Tangent d}
    (h : v =ᵐ[stMeasure d T] v') {p : ℝ × Torus d} (hp : p.1 ≤ T) :
    duhamelOp b F v p = duhamelOp b F v' p := by
  have h1 := Measure.ae_ae_of_ae_prod h
  have h2 : ∀ᵐ s ∂(volume.restrict (Ioo 0 p.1)), ∀ᵐ w ∂haar d, v (s, w) = v' (s, w) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hp) h1
  unfold duhamelOp
  congr 1
  refine integral_congr_ae (h2.mono fun s hs => ?_)
  unfold kerGrad
  refine integral_congr_ae (hs.mono fun w hw => ?_)
  simp only [hw]

theorem integrableOn_sing {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)) (Ioo 0 t) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) (r := -(1 : ℝ) / 2)
    (by norm_num)).comp_sub_left t
  simp only [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1 h.symm

theorem integral_sing {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioo 0 t, (t - s) ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt t := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  ring

theorem rpow_pi_mul {t s : ℝ} (hs : 0 ≤ t - s) :
    (π * (t - s)) ^ (-(1 : ℝ) / 2) = (π) ^ (-(1 : ℝ) / 2) * (t - s) ^ (-(1 : ℝ) / 2) :=
  Real.mul_rpow Real.pi_pos.le hs

theorem time_integral_bound {t : ℝ} (ht : 0 < t) {h : ℝ → Tangent d} {C : ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (Ioo 0 t)))
    (hb : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)), ‖h s‖ ≤ (π * (t - s)) ^ (-(1 : ℝ) / 2) * C) :
    Integrable h (volume.restrict (Ioo 0 t)) ∧
      ‖∫ s in Ioo 0 t, h s‖ ≤ 2 * Real.sqrt (t / π) * C := by
  have hae : (fun s : ℝ => (π * (t - s)) ^ (-(1 : ℝ) / 2) * C) =ᵐ[volume.restrict (Ioo 0 t)]
      fun s => π ^ (-(1 : ℝ) / 2) * (t - s) ^ (-(1 : ℝ) / 2) * C :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => by
      beta_reduce
      rw [rpow_pi_mul (by linarith [hs.2])])
  have hg0 : Integrable (fun s : ℝ => π ^ (-(1 : ℝ) / 2) * (t - s) ^ (-(1 : ℝ) / 2) * C)
      (volume.restrict (Ioo 0 t)) :=
    ((integrableOn_sing ht).const_mul (π ^ (-(1 : ℝ) / 2))).mul_const C
  have hg := hg0.congr hae.symm
  have hpi : π ^ (-(1 : ℝ) / 2) = (Real.sqrt π)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le]; norm_num
  refine ⟨Integrable.mono' hg hh hb, ?_⟩
  refine (norm_integral_le_of_norm_le hg hb).trans (le_of_eq ?_)
  rw [integral_congr_ae hae, integral_mul_const, integral_const_mul, integral_sing ht,
    Real.sqrt_div ht.le, hpi]
  ring

theorem aesm_inner_slice {b : Torus d → Tangent d} (hb : Measurable b) {φ : Torus d → Tangent d}
    (hφ : Measurable φ) : AEStronglyMeasurable (fun w => ⟪b w, φ w⟫) (haar d) :=
  (hb.inner hφ).aestronglyMeasurable

theorem abs_inner_slice_le {b : Torus d → Tangent d} {B0 : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B0)
    {φ : Torus d → Tangent d} {M : ℝ} (hM : ∀ᵐ w ∂haar d, ‖φ w‖ ≤ M) :
    ∀ᵐ w ∂haar d, |⟪b w, φ w⟫| ≤ B0 * M := by
  refine hM.mono fun w hw => ?_
  calc |⟪b w, φ w⟫| ≤ ‖b w‖ * ‖φ w‖ := abs_real_inner_le_norm _ _
    _ ≤ B0 * M := mul_le_mul (hbB w) hw (norm_nonneg _) ((norm_nonneg _).trans (hbB w))

theorem norm_kerGrad_inner_le {τ : ℝ} (hτ : 0 < τ) {b : Torus d → Tangent d} (hb : Measurable b)
    {B0 : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B0) {φ : Torus d → Tangent d} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ᵐ w ∂haar d, ‖φ w‖ ≤ M) (x : Torus d) :
    ‖kerGrad τ (fun w => ⟪b w, φ w⟫) x‖ ≤ (π * τ) ^ (-(1 : ℝ) / 2) * (B0 * M) :=
  norm_kerGrad_le hτ (aesm_inner_slice hb hφ) (abs_inner_slice_le hbB hM) x

theorem norm_kerGrad_inner_sub_le {τ : ℝ} (hτ : 0 < τ) {b : Torus d → Tangent d} (hb : Measurable b)
    {B0 : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B0) {φ ψ : Torus d → Tangent d} (hφ : Measurable φ)
    (hψ : Measurable ψ) {M m : ℝ} (hM : ∀ᵐ w ∂haar d, ‖ψ w‖ ≤ M)
    (hm : ∀ᵐ w ∂haar d, ‖φ w - ψ w‖ ≤ m) (x : Torus d) :
    ‖kerGrad τ (fun w => ⟪b w, φ w⟫) x - kerGrad τ (fun w => ⟪b w, ψ w⟫) x‖ ≤
      (π * τ) ^ (-(1 : ℝ) / 2) * (B0 * m) := by
  have hφM : ∀ᵐ w ∂haar d, ‖φ w‖ ≤ M + m := (hM.and hm).mono fun w hw => by
    have := norm_le_norm_add_norm_sub' (φ w) (ψ w)
    linarith [hw.1, hw.2, norm_sub_rev (φ w) (ψ w)]
  have hi : ∀ {χ : Torus d → Tangent d} {K : ℝ}, Measurable χ → (∀ᵐ w ∂haar d, ‖χ w‖ ≤ K) →
      Integrable (fun w => ⟪b w, χ w⟫) (haar d) := fun {χ K} hχ hK =>
    Integrable.of_bound (aesm_inner_slice hb hχ) (B0 * K)
      ((abs_inner_slice_le hbB hK).mono fun w hw => by rwa [Real.norm_eq_abs])
  rw [← kerGrad_sub hτ (hi hφ hφM) (hi hψ hM)]
  refine norm_kerGrad_le hτ ((aesm_inner_slice hb hφ).sub (aesm_inner_slice hb hψ)) ?_ x
  refine (abs_inner_slice_le hbB hm).mono fun w hw => ?_
  show |⟪b w, φ w⟫ - ⟪b w, ψ w⟫| ≤ _
  rwa [← inner_sub_right]

/-- Contraction estimate (LIP007a (ii)): the pointwise Duhamel difference is bounded by
`2 √(t/π) ‖b‖∞ ‖v - w‖∞`, for measurable `v`, `w` with `w` essentially bounded. -/
theorem duhamelOp_sub_le {T : ℝ} {b : Torus d → Tangent d} {F v w : ℝ × Torus d → Tangent d}
    (hb : Measurable b) {B0 : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B0) (hv : Measurable v) (hw : Measurable w)
    {Mw m : ℝ} (hwb : ∀ᵐ q ∂stMeasure d T, ‖w q‖ ≤ Mw)
    (hm : ∀ᵐ q ∂stMeasure d T, ‖v q - w q‖ ≤ m) {p : ℝ × Torus d} (hp : p.1 ∈ Ioo 0 T) :
    ‖duhamelOp b F v p - duhamelOp b F w p‖ ≤ 2 * Real.sqrt (p.1 / π) * (B0 * m) := by
  obtain ⟨t, x⟩ := p
  have ht : 0 < t := hp.1
  have h1 : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), ∀ᵐ w' ∂haar d,
      ‖v (s, w') - w (s, w')‖ ≤ m ∧ ‖w (s, w')‖ ≤ Mw :=
    Measure.ae_ae_of_ae_prod (hm.and hwb)
  have h2 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hp.2.le) h1
  have h3 : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)), s ∈ Ioo 0 t := ae_restrict_mem measurableSet_Ioo
  have hsl : ∀ (u : ℝ × Torus d → Tangent d), Measurable u → ∀ s : ℝ,
      Measurable fun w' : Torus d => u (s, w') := fun u hu s =>
    hu.comp (measurable_const.prodMk measurable_id)
  have hmeas : ∀ (u : ℝ × Torus d → Tangent d), Measurable u →
      AEStronglyMeasurable (fun s => kerGrad (t - s) (fun w' => ⟪b w', u (s, w')⟫) x)
        (volume.restrict (Ioo 0 t)) := fun u hu =>
    ((stronglyMeasurable_Jint hb hu).comp_measurable
      ((measurable_const (a := ((t, x) : ℝ × Torus d))).prodMk
        (measurable_id : Measurable (id : ℝ → ℝ)))).aestronglyMeasurable
  have hbd : ∀ (u : ℝ × Torus d → Tangent d) (hu : Measurable u) (K : ℝ),
      (∀ s, (∀ᵐ w' ∂haar d, ‖v (s, w') - w (s, w')‖ ≤ m ∧ ‖w (s, w')‖ ≤ Mw) →
        ∀ᵐ w' ∂haar d, ‖u (s, w')‖ ≤ K) →
      Integrable (fun s => kerGrad (t - s) (fun w' => ⟪b w', u (s, w')⟫) x)
        (volume.restrict (Ioo 0 t)) := fun u hu K hK =>
    (time_integral_bound ht (hmeas u hu) (C := B0 * K)
      ((h2.and h3).mono fun s hs => norm_kerGrad_inner_le (by linarith [hs.2.2]) hb hbB (hsl u hu s)
        (hK s hs.1) x)).1
  have hJv := hbd v hv (Mw + m) fun s hs => hs.mono fun w' hw' => by
    have := norm_le_norm_add_norm_sub' (v (s, w')) (w (s, w'))
    linarith [hw'.1, hw'.2, norm_sub_rev (v (s, w')) (w (s, w'))]
  have hJw := hbd w hw Mw fun s hs => hs.mono fun w' hw' => hw'.2
  have hfin := (time_integral_bound ht (C := B0 * m)
    ((hmeas v hv).sub (hmeas w hw))
    ((h2.and h3).mono fun s hs => by
      have hτ : 0 < t - s := by linarith [hs.2.2]
      exact norm_kerGrad_inner_sub_le hτ hb hbB (hsl v hv s) (hsl w hw s) (M := Mw) (m := m)
        (hs.1.mono fun w' hw' => hw'.2) (hs.1.mono fun w' hw' => hw'.1) x)).2
  unfold duhamelOp
  rw [add_sub_add_left_eq_sub, ← integral_sub hJv hJw]
  exact hfin

theorem duhamelOp_zero (b : Torus d → Tangent d) (F : ℝ × Torus d → Tangent d) (p : ℝ × Torus d) :
    duhamelOp b F 0 p = F p := by
  simp [duhamelOp, kerGrad]

theorem ae_mem_stMeasure (T : ℝ) : ∀ᵐ q ∂stMeasure d T, q.1 ∈ Ioo 0 T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)

theorem ae_of_forall_mem {T : ℝ} {P : ℝ × Torus d → Prop} (h : ∀ p, p.1 ∈ Ioo 0 T → P p) :
    ∀ᵐ q ∂stMeasure d T, P q :=
  (ae_mem_stMeasure T).mono h

theorem norm_duhamelOp_sub_le {T : ℝ} {b : Torus d → Tangent d} {F v : ℝ × Torus d → Tangent d}
    (hb : Measurable b) {B0 : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B0) (hv : Measurable v) {Mv : ℝ}
    (hvb : ∀ᵐ q ∂stMeasure d T, ‖v q‖ ≤ Mv) {p : ℝ × Torus d} (hp : p.1 ∈ Ioo 0 T) :
    ‖duhamelOp b F v p - F p‖ ≤ 2 * Real.sqrt (p.1 / π) * (B0 * Mv) := by
  have := duhamelOp_sub_le (F := F) (w := 0) hb hbB hv measurable_zero (Mw := 0) (m := Mv)
    (Filter.Eventually.of_forall fun q => by simp) (hvb.mono fun q hq => by simpa using hq) hp
  rwa [duhamelOp_zero] at this

theorem sqrt_le_kappa {T t B0 : ℝ} (hB0 : 0 ≤ B0) (ht : t ≤ T) :
    2 * Real.sqrt (t / π) * B0 ≤ 2 * B0 * Real.sqrt (T / π) := by
  have : Real.sqrt (t / π) ≤ Real.sqrt (T / π) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht Real.pi_pos.le)
  nlinarith [Real.sqrt_nonneg (t / π), Real.sqrt_nonneg (T / π)]

/-- Picard iterates `u₀ = 0`, `u_{n+1} = 1_{t<T} Φ(u_n)`. -/
noncomputable def picard (T : ℝ) (b : Torus d → Tangent d) (F : ℝ × Torus d → Tangent d) :
    ℕ → ℝ × Torus d → Tangent d
  | 0 => 0
  | n + 1 => Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F (picard T b F n))

section Picard

variable {T : ℝ} {b : Torus d → Tangent d} {F : ℝ × Torus d → Tangent d} {B0 M : ℝ}

theorem measurableSet_slab (T : ℝ) : MeasurableSet {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} :=
  measurableSet_Ioo.preimage measurable_fst

theorem step_bound (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ M) (hM : 0 ≤ M)
    (hκ : 2 * B0 * Real.sqrt (T / π) ≤ 1 / 2) {u : ℝ × Torus d → Tangent d} (hu : Measurable u)
    (hub : ∀ p, ‖u p‖ ≤ 2 * M) (p : ℝ × Torus d) :
    ‖Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F u) p‖ ≤ 2 * M := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  by_cases hp : p.1 ∈ Ioo 0 T
  · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp)]
    have h1 := norm_duhamelOp_sub_le (F := F) hb hbB hu (Mv := 2 * M)
      (Filter.Eventually.of_forall hub) hp
    have h2 := sqrt_le_kappa (T := T) hB0 hp.2.le
    have h3 : 2 * Real.sqrt (p.1 / π) * (B0 * (2 * M)) ≤ M := by
      calc 2 * Real.sqrt (p.1 / π) * (B0 * (2 * M)) = (2 * Real.sqrt (p.1 / π) * B0) * (2 * M) := by
            ring
        _ ≤ (2 * B0 * Real.sqrt (T / π)) * (2 * M) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ (1 / 2) * (2 * M) := mul_le_mul_of_nonneg_right hκ (by positivity)
        _ = M := by ring
    calc ‖duhamelOp b F u p‖ ≤ ‖F p‖ + ‖duhamelOp b F u p - F p‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ M + M := add_le_add (hFM p hp) (h1.trans h3)
      _ = 2 * M := by ring
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp)]
    simpa using hM.trans (by linarith)

theorem step_diff (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) {u w : ℝ × Torus d → Tangent d}
    (hu : Measurable u) (hw : Measurable w) {Mw m : ℝ} (hwb : ∀ p, ‖w p‖ ≤ Mw)
    (hm : ∀ p, ‖u p - w p‖ ≤ m) (hm0 : 0 ≤ m) (p : ℝ × Torus d) :
    ‖Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F u) p -
      Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F w) p‖ ≤
      (2 * B0 * Real.sqrt (T / π)) * m := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  by_cases hp : p.1 ∈ Ioo 0 T
  · simp only [Set.indicator_of_mem (show p ∈ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp)]
    refine (duhamelOp_sub_le hb hbB hu hw (T := T) (Filter.Eventually.of_forall hwb)
      (Filter.Eventually.of_forall hm) hp).trans ?_
    calc 2 * Real.sqrt (p.1 / π) * (B0 * m) = (2 * Real.sqrt (p.1 / π) * B0) * m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (sqrt_le_kappa hB0 hp.2.le) hm0
  · simp only [Set.indicator_of_notMem (show p ∉ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp),
      sub_self, norm_zero]
    positivity

theorem picard_props (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) (hF : Measurable F)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ M) (hM : 0 ≤ M)
    (hκ : 2 * B0 * Real.sqrt (T / π) ≤ 1 / 2) :
    ∀ n, Measurable (picard T b F n) ∧ (∀ p, ‖picard T b F n p‖ ≤ 2 * M) ∧
      ∀ p, ‖picard T b F (n + 1) p - picard T b F n p‖ ≤
        2 * M * (2 * B0 * Real.sqrt (T / π)) ^ n := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hκ0 : 0 ≤ 2 * B0 * Real.sqrt (T / π) := by positivity
  intro n
  induction n with
  | zero =>
    have h0 : Measurable (0 : ℝ × Torus d → Tangent d) := measurable_const
    refine ⟨by simpa [picard] using h0, fun p => by simpa [picard] using (by linarith : (0 : ℝ) ≤ 2 * M), fun p => ?_⟩
    have := step_bound hb hbB hFM hM hκ h0 (u := 0)
      (fun p => by simpa using (by linarith : (0 : ℝ) ≤ 2 * M)) p
    simpa [picard] using this
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hmeas : Measurable (picard T b F (n + 1)) :=
      (measurable_duhamelOp hb hF h1).indicator (measurableSet_slab T)
    refine ⟨hmeas, fun p => step_bound hb hbB hFM hM hκ h1 h2 p, fun p => ?_⟩
    have := step_diff (F := F) (T := T) hb hbB hmeas h1 h2 h3 (by positivity) p
    calc _ ≤ _ := this
      _ = _ := by ring

open Filter Topology in
theorem exists_fixed_point (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) (hF : Measurable F)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ M) (hM : 0 ≤ M)
    (hκ : 2 * B0 * Real.sqrt (T / π) ≤ 1 / 2) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * M) ∧
      ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b F v p = v p := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  set κ := 2 * B0 * Real.sqrt (T / π) with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := by linarith
  have hP := picard_props hb hbB hF hFM hM hκ
  have hu : ∀ p n, dist (picard T b F n p) (picard T b F (n + 1) p) ≤ 2 * M * κ ^ n :=
    fun p n => by rw [dist_comm, dist_eq_norm]; exact (hP n).2.2 p
  have hc : ∀ p, ∃ a, Tendsto (fun n => picard T b F n p) atTop (𝓝 a) := fun p =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric κ (2 * M) hκ1 (hu p))
  choose v hv using hc
  have hvm : Measurable v :=
    measurable_of_tendsto_metrizable (fun n => (hP n).1) (tendsto_pi_nhds.2 hv)
  have hvb : ∀ p, ‖v p‖ ≤ 2 * M := fun p =>
    le_of_tendsto (hv p).norm (Eventually.of_forall fun n => (hP n).2.1 p)
  have hd : ∀ p n, ‖picard T b F n p - v p‖ ≤ 4 * M * κ ^ n := fun p n => by
    have := dist_le_of_le_geometric_of_tendsto κ (2 * M) hκ1 (hu p) (hv p) n
    rw [dist_eq_norm] at this
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hM (pow_nonneg hκ0 n)]
  refine ⟨v, hvm, hvb, fun p hp => ?_⟩
  have hbound : ∀ n, ‖duhamelOp b F v p - v p‖ ≤ 8 * M * κ ^ n := fun n => by
    have hpic : duhamelOp b F (picard T b F n) p = picard T b F (n + 1) p := by
      simp only [picard]
      rw [Set.indicator_of_mem (show p ∈ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp)]
    have h1 := duhamelOp_sub_le (T := T) (F := F) hb hbB hvm (hP n).1 (Mw := 2 * M)
      (m := 4 * M * κ ^ n) (Filter.Eventually.of_forall fun q => (hP n).2.1 q)
      (Filter.Eventually.of_forall fun q => by rw [norm_sub_rev]; exact hd q n) hp
    have h2 : 2 * Real.sqrt (p.1 / π) * (B0 * (4 * M * κ ^ n)) ≤ 4 * M * κ ^ n := by
      have hm0 : 0 ≤ 4 * M * κ ^ n := by positivity
      calc 2 * Real.sqrt (p.1 / π) * (B0 * (4 * M * κ ^ n))
          = (2 * Real.sqrt (p.1 / π) * B0) * (4 * M * κ ^ n) := by ring
        _ ≤ κ * (4 * M * κ ^ n) := mul_le_mul_of_nonneg_right
            (by rw [hκdef]; exact sqrt_le_kappa hB0 hp.2.le) hm0
        _ ≤ 1 * (4 * M * κ ^ n) := mul_le_mul_of_nonneg_right hκ1.le hm0
        _ = _ := one_mul _
    have h3 : ‖duhamelOp b F (picard T b F n) p - v p‖ ≤ 4 * M * κ ^ n := by
      rw [hpic]
      refine (hd p (n + 1)).trans ?_
      rw [pow_succ]
      nlinarith [mul_nonneg hM (pow_nonneg hκ0 n)]
    calc ‖duhamelOp b F v p - v p‖
        ≤ ‖duhamelOp b F v p - duhamelOp b F (picard T b F n) p‖ +
          ‖duhamelOp b F (picard T b F n) p - v p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 8 * M * κ ^ n := by linarith
  have hlim : Tendsto (fun n : ℕ => 8 * M * κ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul (8 * M)
  have := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

open Filter Topology in
theorem fixed_point_unique (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hκ : 2 * B0 * Real.sqrt (T / π) ≤ 1 / 2) {u v : ℝ × Torus d → Tangent d}
    (hu : Measurable u) (hv : Measurable v) {Mu Mv : ℝ}
    (hub : ∀ᵐ q ∂stMeasure d T, ‖u q‖ ≤ Mu) (hvb : ∀ᵐ q ∂stMeasure d T, ‖v q‖ ≤ Mv)
    (hfu : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b F u p = u p)
    (hfv : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b F v p = v p) :
    u =ᵐ[stMeasure d T] v := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  set κ := 2 * B0 * Real.sqrt (T / π) with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := by linarith
  have hD : ∀ᵐ q ∂stMeasure d T, ‖u q - v q‖ ≤ Mu + Mv := (hub.and hvb).mono fun q hq =>
    (norm_sub_le _ _).trans (add_le_add hq.1 hq.2)
  have key : ∀ k : ℕ, ∀ᵐ q ∂stMeasure d T, ‖u q - v q‖ ≤ (Mu + Mv) * κ ^ k := by
    intro k
    induction k with
    | zero => simpa using hD
    | succ k ih =>
      filter_upwards [ae_mem_stMeasure T, ih] with q hq hqk
      have hm : ∀ᵐ r ∂stMeasure d T, ‖u r - v r‖ ≤ (Mu + Mv) * κ ^ k := ih
      have h1 := duhamelOp_sub_le (T := T) (F := F) hb hbB hu hv hvb hm hq
      rw [hfu q hq, hfv q hq] at h1
      have hm0 : 0 ≤ (Mu + Mv) * κ ^ k := (norm_nonneg _).trans hqk
      refine h1.trans ?_
      calc 2 * Real.sqrt (q.1 / π) * (B0 * ((Mu + Mv) * κ ^ k))
          = (2 * Real.sqrt (q.1 / π) * B0) * ((Mu + Mv) * κ ^ k) := by ring
        _ ≤ κ * ((Mu + Mv) * κ ^ k) := mul_le_mul_of_nonneg_right
            (by rw [hκdef]; exact sqrt_le_kappa hB0 hq.2.le) hm0
        _ = (Mu + Mv) * κ ^ (k + 1) := by ring
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with q hq
  have hlim : Tendsto (fun n : ℕ => (Mu + Mv) * κ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul (Mu + Mv)
  have := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hq
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-! ### The free term and the main theorem -/

/-- The free term `(t, x) ↦ ∇ H_t f (x)`, as a `Tangent d`-valued function on space-time. -/
noncomputable def heatGrad (f : Torus d → ℝ) (p : ℝ × Torus d) : Tangent d :=
  kerGrad p.1 f p.2

theorem measurable_heatGrad {f : Torus d → ℝ} (hf : Measurable f) : Measurable (heatGrad f) := by
  have hI : Measurable fun q : (ℝ × Torus d) × Torus d =>
      f q.2 • Dk q.1.1 (secE q.1.2 - secE q.2) := by
    refine Measurable.smul
      (f := fun q : (ℝ × Torus d) × Torus d => f q.2)
      (g := fun q : (ℝ × Torus d) × Torus d => Dk q.1.1 (secE q.1.2 - secE q.2)) ?_ ?_
    · exact hf.comp measurable_snd
    · refine measurable_Dk.comp (Measurable.prodMk ?_ ?_)
      · exact measurable_fst.comp measurable_fst
      · exact (measurable_secE.comp (measurable_snd.comp measurable_fst)).sub
          (measurable_secE.comp measurable_snd)
  exact hI.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_heatGrad_le {L : ℝ} (hL : 0 ≤ L) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f)
    {p : ℝ × Torus d} (hp : 0 < p.1) : ‖heatGrad f p‖ ≤ L := by
  have hc := continuous_of_torusLipschitz hL hf
  have hfi : Integrable f (haar d) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  unfold heatGrad
  rw [norm_kerGrad hp hfi]
  exact ((periodized_heat_gradient_bounds hp).2.1 hL hf (secE p.2)).2

/-- The gradient identification: `heatGrad f (t, x)` is the Riesz representative of the Fréchet
derivative of `v ↦ H_t f (v)` at `secE x`. -/
theorem toDual_heatGrad {f : Torus d → ℝ} (hfi : Integrable f (haar d)) {t : ℝ} (ht : 0 < t)
    (x : Torus d) :
    HasFDerivAt (Hl t f) (InnerProductSpace.toDual ℝ (Tangent d) (heatGrad f (t, x))) (secE x) := by
  have h := hasFDerivAt_Hl ht hfi (secE x)
  rwa [← toDual_kerGrad ht hfi x] at h

theorem kappa_le_half {T B0 : ℝ} (hT : 0 < T) (h : 16 * B0 ^ 2 * T ≤ π) :
    2 * B0 * Real.sqrt (T / π) ≤ 1 / 2 := by
  have hs : Real.sqrt (T / π) ^ 2 = T / π := Real.sq_sqrt (by positivity)
  have hs0 := Real.sqrt_nonneg (T / π)
  have h1 : T / π * 16 * B0 ^ 2 ≤ 1 := by
    have : T / π * 16 * B0 ^ 2 = 16 * B0 ^ 2 * T / π := by ring
    rw [this, div_le_one Real.pi_pos]; exact h
  have h2 : (2 * |B0| * Real.sqrt (T / π)) ^ 2 ≤ (1 / 2) ^ 2 := by
    have : (2 * |B0| * Real.sqrt (T / π)) ^ 2 = 4 * B0 ^ 2 * (T / π) := by
      rw [mul_pow, mul_pow, hs, sq_abs]; ring
    rw [this]; nlinarith
  have h3 := abs_le_of_sq_le_sq' h2 (by norm_num)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self B0) (by norm_num)) hs0).trans h3.2

/-- **LIP007a.** Let `b : 𝕋^d → ℝ^d` be measurable with `‖b‖ ≤ B0`, `f` be `L`-Lipschitz, `0 < T`
and `16 B0² T ≤ π`.  Write `Φ v = ∇H_t f + ∫₀ᵗ ∇H_{t-s}(b · v(s)) ds` and `ν = Leb|(0,T) ⊗ haar`.
(i) `Φ` preserves measurability and `Φ v (p)` depends only on the `ν`-class of `v` (for `p.1 ≤ T`);
(ii) for measurable `v`, `w` with `‖w‖ ≤ Mw`, `‖v - w‖ ≤ m` `ν`-a.e., one has for `0 < t < T` the
bound `‖Φ v (t,x) - Φ w (t,x)‖ ≤ 2 √(t/π) B0 m`, hence `≤ m/2` (a contraction);
(iii) there is a measurable fixed point `v` with `‖v‖ ≤ 2L` on space-time, `Φ v = v` on `0 < t < T`,
and every measurable, essentially bounded `u` with `u = Φ u` `ν`-a.e. equals `v` `ν`-a.e. -/
theorem lip007a_duhamel_fixed_point {T B0 L : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    {b : Torus d → Tangent d} (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) (hTB : 16 * B0 ^ 2 * T ≤ π)
    {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ((∀ v, Measurable v → Measurable (duhamelOp b (heatGrad f) v)) ∧
      (∀ v v' : ℝ × Torus d → Tangent d, v =ᵐ[stMeasure d T] v' → ∀ p : ℝ × Torus d, p.1 ≤ T →
        duhamelOp b (heatGrad f) v p = duhamelOp b (heatGrad f) v' p)) ∧
    (∀ v w : ℝ × Torus d → Tangent d, Measurable v → Measurable w → ∀ Mw m : ℝ,
      (∀ᵐ q ∂stMeasure d T, ‖w q‖ ≤ Mw) → (∀ᵐ q ∂stMeasure d T, ‖v q - w q‖ ≤ m) →
      ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
        ‖duhamelOp b (heatGrad f) v p - duhamelOp b (heatGrad f) w p‖ ≤
          2 * Real.sqrt (p.1 / π) * (B0 * m) ∧
        (0 ≤ m → ‖duhamelOp b (heatGrad f) v p - duhamelOp b (heatGrad f) w p‖ ≤ m / 2)) ∧
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
      (∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b (heatGrad f) v p = v p) ∧
      ∀ u : ℝ × Torus d → Tangent d, Measurable u → (∃ Mu, ∀ᵐ q ∂stMeasure d T, ‖u q‖ ≤ Mu) →
        u =ᵐ[stMeasure d T] duhamelOp b (heatGrad f) u → u =ᵐ[stMeasure d T] v := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hκ := kappa_le_half hT hTB
  have hF : Measurable (heatGrad f) := measurable_heatGrad (continuous_of_torusLipschitz hL hf).measurable
  have hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖heatGrad f p‖ ≤ L := fun p hp =>
    norm_heatGrad_le hL hf hp.1
  refine ⟨⟨fun v hv => measurable_duhamelOp hb hF hv, fun v v' h p hp => duhamelOp_congr h hp⟩,
    fun v w hv hw Mw m hwb hm p hp => ⟨duhamelOp_sub_le hb hbB hv hw hwb hm hp, fun hm0 => ?_⟩, ?_⟩
  · refine (duhamelOp_sub_le hb hbB hv hw hwb hm hp).trans ?_
    calc 2 * Real.sqrt (p.1 / π) * (B0 * m) = (2 * Real.sqrt (p.1 / π) * B0) * m := by ring
      _ ≤ (2 * B0 * Real.sqrt (T / π)) * m := mul_le_mul_of_nonneg_right (sqrt_le_kappa hB0 hp.2.le) hm0
      _ ≤ (1 / 2) * m := mul_le_mul_of_nonneg_right hκ hm0
      _ = m / 2 := by ring
  · obtain ⟨v, hvm, hvb, hvf⟩ := exists_fixed_point hb hbB hF hFM hL hκ
    refine ⟨v, hvm, hvb, hvf, fun u hu ⟨Mu, hub⟩ hae => ?_⟩
    have hu' : Measurable (duhamelOp b (heatGrad f) u) := measurable_duhamelOp hb hF hu
    have hub' : ∀ᵐ q ∂stMeasure d T, ‖duhamelOp b (heatGrad f) u q‖ ≤ Mu := by
      filter_upwards [hub, hae] with q h1 h2
      rwa [← h2]
    have hfu' : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
        duhamelOp b (heatGrad f) (duhamelOp b (heatGrad f) u) p = duhamelOp b (heatGrad f) u p :=
      fun p hp => duhamelOp_congr hae.symm hp.2.le
    exact hae.trans (fixed_point_unique hb hbB hκ hu' hvm hub' (Filter.Eventually.of_forall hvb)
      hfu' hvf)

end Picard

end DGPS.Lipschitz
