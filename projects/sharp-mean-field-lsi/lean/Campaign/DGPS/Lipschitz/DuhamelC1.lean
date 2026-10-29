import DGPS.Lipschitz.DuhamelPotential
import DGPS.Lipschitz.Representatives

/-!
# LIP007c: continuous gradient and `C¹` representative of the Duhamel potential

For `0 < t < T` the Duhamel gradient `x ↦ v (t, x)` is continuous (split the time integral at
`t - ε`), and a function with a continuous weak gradient (and bounded) has a `C¹` representative
whose classical gradient is that weak gradient.
-/

open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace ENNReal
namespace DGPS.Lipschitz
open DGPS.Lipschitz.ParabolicChainRule
variable {d : ℕ}

/-! ### `C¹` as a uniform limit of smooth functions -/

theorem fderiv_eq_sum_coordPartial (φ : Torus d → ℝ) (z : Fin d → ℝ) :
    fderiv ℝ (φ ∘ torusLift) z =
      ∑ j, coordPartial j φ (torusLift z) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun y => ?_
  have e : y = ∑ j, y j • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [e]
  rw [map_sum, sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, ← congrFun (coordPartial_comp_torusLift j φ) z]
  simp [mul_comm]

theorem isC1Periodic_of_uniform_limit {w : Torus d → ℝ} {g : Torus d → Tangent d}
    (hgc : Continuous g) {wn : ℕ → Torus d → ℝ} (hsm : ∀ n, IsSmoothPeriodic (wn n))
    (hw : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, dist (wn n x) (w x) < ε)
    (hg : ∀ j : Fin d, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, dist (coordPartial j (wn n) x) (g x j) < ε) :
    IsC1Periodic w ∧ ∀ x j, coordPartial j w x = g x j := by
  set f' : ℕ → (Fin d → ℝ) → ((Fin d → ℝ) →L[ℝ] ℝ) := fun n z =>
    ∑ j, coordPartial j (wn n) (torusLift z) • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)
    with hf'
  set g' : (Fin d → ℝ) → ((Fin d → ℝ) →L[ℝ] ℝ) := fun z =>
    ∑ j, g (torusLift z) j • (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ) with hg'
  have hunif : TendstoUniformly f' g' atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    set ε' : ℝ := ε / (2 * ((d : ℝ) + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hall : ∀ᶠ n in atTop, ∀ j : Fin d, ∀ x, dist (coordPartial j (wn n) x) (g x j) < ε' :=
      Filter.eventually_all.2 fun j => hg j ε' hε'0
    filter_upwards [hall] with n hn z
    rw [dist_eq_norm]
    have : g' z - f' n z = ∑ j, (g (torusLift z) j - coordPartial j (wn n) (torusLift z)) •
        (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ) := by
      simp only [hg', hf']
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (sub_smul _ _ _).symm
    rw [this]
    refine lt_of_le_of_lt ?_ (show (d : ℝ) * ε' < ε by
      rw [hε']
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    rw [sum_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖((g (torusLift z) j - coordPartial j (wn n) (torusLift z)) •
          (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ)) y‖
        ≤ ∑ _j : Fin d, ε' * ‖y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
            norm_mul]
          refine mul_le_mul ?_ (norm_le_pi_norm y j) (norm_nonneg _) hε'0.le
          have := hn j (torusLift z)
          rw [Real.dist_eq, abs_sub_comm] at this
          rw [Real.norm_eq_abs]
          exact this.le
      _ = d * ε' * ‖y‖ := by simp [Finset.sum_const]; ring
  have hderiv : ∀ n z, HasFDerivAt (wn n ∘ torusLift) (f' n z) z := by
    intro n z
    have h := ((hsm n).differentiable (by simp) z).hasFDerivAt
    rwa [fderiv_eq_sum_coordPartial (wn n) z] at h
  have hpt : ∀ z, Tendsto (fun n => (wn n ∘ torusLift) z) atTop (𝓝 ((w ∘ torusLift) z)) := by
    intro z
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hw ε hε] with n hn using hn (torusLift z)
  have hfd := fun z => hasFDerivAt_of_tendstoUniformly hunif hderiv hpt z
  have hcont : Continuous g' := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact (((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.comp
      (hgc.comp (SharpLSI.continuous_liftT)))).smul continuous_const
  have hC1 : IsC1Periodic w := by
    unfold IsC1Periodic
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hfd z).differentiableAt, ?_⟩
    have : fderiv ℝ (w ∘ torusLift) = g' := funext fun z => (hfd z).fderiv
    rw [this]; exact hcont
  refine ⟨hC1, fun x j => ?_⟩
  show fderiv ℝ (w ∘ SharpLSI.liftT) (SharpLSI.secT x) (Pi.single j 1) = _
  have := (hfd (SharpLSI.secT x)).fderiv
  change fderiv ℝ (w ∘ torusLift) (SharpLSI.secT x) = _ at this
  rw [this]
  simp [hg', SharpLSI.liftT_secT, Pi.single_apply]

/-- A bounded function with a continuous `L²` weak gradient `g` has a `C¹` representative whose
classical gradient is `g`. -/
theorem exists_isC1Periodic_of_continuous_weakGradient {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (hgc : Continuous g) (hu : MemLp u ∞ (haar d)) :
    ∃ w : Torus d → ℝ, IsC1Periodic w ∧ w =ᵐ[haar d] u ∧ ∀ x j, coordPartial j w x = g x j := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hgc.continuousOn
  have hM' : ∀ x, ‖g x‖ ≤ max M 0 := fun x => (hM x (mem_univ x)).trans (le_max_left _ _)
  have hgtop : MemLp g ∞ (haar d) :=
    memLp_top_of_bound hgc.aestronglyMeasurable (max M 0) (Eventually.of_forall hM')
  have hLp : IsWeakGradientLp ∞ u g := ⟨hu, hgtop, hg.ibp⟩
  obtain ⟨w, hwc, hwae, -⟩ := exists_lipschitz_rep hLp (le_max_right M 0)
    (Eventually.of_forall hM')
  have hwi : Integrable w (haar d) := integrable_of_continuous_torus hwc
  have hgj : ∀ j, Continuous fun x => g x j := fun j =>
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.comp hgc
  have hdw : ∀ n j, coordPartial j (SharpLSI.moll n w) = SharpLSI.moll n (fun x => g x j) := by
    intro n j
    refine coordPartial_moll_of_ibp hwi (integrable_of_continuous_torus (hgj j)) j ?_ n
    intro φ hφ
    rw [← hg.ibp φ hφ j]
    refine integral_congr_ae ?_
    filter_upwards [hwae] with x hx
    rw [hx]
  have hu1 : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, dist (SharpLSI.moll n w x) (w x) < ε := by
    intro ε hε
    filter_upwards [SharpLSI.moll_uniform_of_continuous hwc (half_pos hε)] with n hn x
    exact (hn x).trans_lt (half_lt_self hε)
  have hu2 : ∀ j : Fin d, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ x, dist (coordPartial j (SharpLSI.moll n w) x) (g x j) < ε := by
    intro j ε hε
    filter_upwards [SharpLSI.moll_uniform_of_continuous (hgj j) (half_pos hε)] with n hn x
    rw [hdw]
    exact (hn x).trans_lt (half_lt_self hε)
  obtain ⟨h1, h2⟩ := isC1Periodic_of_uniform_limit hgc
    (fun n => isSmoothPeriodic_moll n hwi) hu1 hu2
  exact ⟨w, h1, hwae, h2⟩

/-! ### Continuity of the gradient slice -/

theorem continuous_kerGrad {τ : ℝ} (hτ : 0 < τ) {g : Torus d → ℝ} (hg : Integrable g (haar d)) :
    Continuous (kerGrad τ g) := by
  have h : ∀ j : Fin d, Continuous fun x => kerGrad τ g x j := fun j => by
    have hc := (isC1Periodic_heatOp hτ hg).continuous_coordPartial j
    have : (fun x => kerGrad τ g x j) = coordPartial j (heatOp τ g) := by
      funext x
      rw [lip026b_coordPartial_heatOp hτ hg j x, kerGrad_apply hτ hg x j]
    rw [this]; exact hc
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

theorem continuous_duhamel_gradient {T B0 V : ℝ} {b : Torus d → Tangent d}
    (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hfc : Continuous f)
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V)
    (hfix : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b (heatGrad f) v p = v p)
    {t : ℝ} (ht : t ∈ Ioo 0 T) : Continuous fun x => v (t, x) := by
  have ht0 : 0 < t := ht.1
  have hfi : Integrable f (haar d) := integrable_of_continuous_torus hfc
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) t) with hμ
  have hv' : ∀ x, v (t, x) = kerGrad t f x + ∫ s, Jint b v ((t, x), s) ∂μ := fun x =>
    (hfix (t, x) ht).symm
  have hI : Continuous fun x => ∫ s, Jint b v ((t, x), s) ∂μ := by
    refine continuous_of_dominated (bound := fun s => π ^ (-(1 : ℝ) / 2) * (t - s) ^ (-(1 : ℝ) / 2) * (B0 * V))
      (fun x => ((stronglyMeasurable_Jint hb hv).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_ ?_ ?_
    · intro x
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => ?_)
      have h2 := norm_Jint_le hb hv hbB hvV hs x
      rwa [rpow_pi_mul (by linarith [hs.2])] at h2
    · exact ((integrableOn_sing ht0).const_mul _).mul_const _
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun s hs => ?_)
      have hτ : 0 < t - s := by linarith [hs.2]
      show Continuous fun x => kerGrad (t - s) (fun w => ⟪b w, v (s, w)⟫) x
      exact continuous_kerGrad hτ (integrable_gSlice hb hv hbB hvV s)
  have : (fun x => v (t, x)) = fun x => kerGrad t f x + ∫ s, Jint b v ((t, x), s) ∂μ :=
    funext hv'
  rw [this]
  exact (continuous_kerGrad ht0 hfi).add hI

/-! ### Boundedness of the Duhamel potential -/

theorem memLp_top_duhamelPotential {B0 V : ℝ} {b : Torus d → Tangent d}
    (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hfc : Continuous f)
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V)
    {t : ℝ} (ht0 : 0 < t) : MemLp (duhamelPotential b f v t) ∞ (haar d) := by
  have hfi : Integrable f (haar d) := integrable_of_continuous_torus hfc
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) t) with hμ
  have hcont : Continuous (heatOp t f) := (isC1Periodic_heatOp ht0 hfi).continuous_torus
  have hJ0m : StronglyMeasurable fun z : Torus d × ℝ => Jint0 b v ((t, z.1), z.2) :=
    (stronglyMeasurable_Jint0 hb hv).comp_measurable
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
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
  obtain ⟨Cf, -, hCf⟩ := exists_abs_le_of_continuous' hfc
  have hmeas : AEStronglyMeasurable (duhamelPotential b f v t) (haar d) := by
    have : duhamelPotential b f v t = fun x => heatOp t f x + ∫ s, Jint0 b v ((t, x), s) ∂μ :=
      funext fun x => duhamelPotential_eq b f v x
    rw [this]
    exact (hcont.aestronglyMeasurable).add hUm.aestronglyMeasurable
  refine memLp_top_of_bound hmeas (Cf + B0 * V * t) (Filter.Eventually.of_forall fun x => ?_)
  rw [duhamelPotential_eq]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hUb x))
  rw [Real.norm_eq_abs]
  exact abs_heatOp_le ht0 hCf x

/-- **LIP007c.** Under the hypotheses of `lip007b_mild_gradient`, for every `0 < t < T` the slice
`x ↦ v (t, x)` of the fixed point is continuous, and the Duhamel potential `u(t)` has a `C¹`
representative (equal to it a.e.) whose gradient is `v (t, ·)` itself. -/
theorem lip007c_continuous_gradient_representative {T B0 L : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    {b : Torus d → Tangent d} (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hTB : 16 * B0 ^ 2 * T ≤ π) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
      (∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b (heatGrad f) v p = v p) ∧
      ∀ t ∈ Ioo 0 T, Continuous (fun x => v (t, x)) ∧
        ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧ ũ =ᵐ[haar d] duhamelPotential b f v t ∧
          ∀ x j, coordPartial j ũ x = v (t, x) j := by
  obtain ⟨v, hvm, hvb, hvf, -, hw⟩ := lip007b_mild_gradient hT hL hb hbB hTB hf
  have hfc := continuous_of_torusLipschitz hL hf
  refine ⟨v, hvm, hvb, hvf, fun t ht => ?_⟩
  have hc := continuous_duhamel_gradient hb hbB hfc hvm hvb hvf ht
  have hgc : Continuous fun x => v (t, x) := hc
  obtain ⟨w, h1, h2, h3⟩ := exists_isC1Periodic_of_continuous_weakGradient (hw t ht) hgc
    (memLp_top_duhamelPotential hb hbB hfc hvm hvb ht.1)
  exact ⟨hc, w, h1, h2, h3⟩

end DGPS.Lipschitz
