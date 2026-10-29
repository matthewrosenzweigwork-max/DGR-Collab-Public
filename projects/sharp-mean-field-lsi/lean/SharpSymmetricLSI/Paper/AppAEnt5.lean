import SharpSymmetricLSI.Paper.AppAEnt4

/-!
# The entropy (5): the free-energy identity at level `(ε, δ)`

With `φ_u = e^{εΔ}ρ_u`, `ψ_u = e^{εΔ}N_u`, the regularized free energy
`E_{ε,δ}(f) = ∫ (G_δ(e^{εΔ}f) + V e^{εΔ}f) + ½ ∬ W e^{εΔ}f ⊗ e^{εΔ}f` satisfies
`E_{ε,δ}(ρ_t) = E_{ε,δ}(ρ₀) - ∫_{(0,t]} R_{ε,δ}(u) du` (`LinMild.eps_identity`), where
`R_{ε,δ}(u) = ∑ⱼ ∫ (G_δ''(φ_u) ∂ⱼφ_u + ∂ⱼV + ∂ⱼ(W*φ_u)) (∂ⱼφ_u + ψ_{u,j})`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

theorem abs_integral_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M) : |∫ x, f x ∂μ| ≤ M := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := M)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)).trans ?_
  simp

theorem integrableOn_Ioc_of_abs_le {F : ℝ → ℝ} (hF : Measurable F) {t M : ℝ}
    (hb : ∀ u ∈ Ioc 0 t, |F u| ≤ M) : IntegrableOn F (Ioc 0 t) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact (integrable_const M).mono' hF.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs]; exact hb u hu))

theorem continuous_entGp (δ : ℝ) : Continuous (entGp δ) :=
  Real.continuous_arsinh.comp (continuous_id.div_const δ)

theorem continuous_entG {δ : ℝ} (hδ : 0 < δ) : Continuous (entG δ) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_entG hδ r).continuousAt

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The regularized free energy at level `(ε, δ)`. -/
noncomputable def epsE (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (δ ε : ℝ)
    (f : Torus d → ℝ) : ℝ :=
  (∫ x, (entG δ (heatT ε f x) + V x * heatT ε f x)) +
    (∫ p, W p.1 p.2 * (heatT ε f p.1 * heatT ε f p.2) ∂(volume.prod volume)) / 2

/-- The dissipation rate at level `(ε, δ)`. -/
noncomputable def epsRate (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (δ ε : ℝ)
    (f : Torus d → ℝ) (F : Torus d → Fin d → ℝ) : ℝ :=
  ∑ j, ∫ x, (entGpp δ (heatT ε f x) * dpart_appA (heatT ε f) j x + lipGrad V x j +
      bForceL W (heatT ε f) x j) * (dpart_appA (heatT ε f) j x + heatT ε (fun z => F z j) x)

theorem abs_convDens_le {MW : ℝ} (hMW : ∀ x y, |W x y| ≤ MW) {f : Torus d → ℝ}
    (hf : Integrable f (haar d)) (x : Torus d) :
    |convDens W f x| ≤ MW * ∫ y, |f y| ∂haar d := by
  unfold convDens
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.abs.const_mul MW) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hMW x y) (abs_nonneg _)

theorem appA_abs_bForceL_le {Cb : ℝ} (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb) {f : Torus d → ℝ}
    (hf : Integrable f (haar d)) (x : Torus d) (k : Fin d) :
    |bForceL W f x k| ≤ Cb * ∫ y, |f y| ∂haar d := by
  unfold bForceL
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.abs.const_mul Cb) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _)

namespace LinMild

variable {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {N : ℝ → Torus d → Fin d → ℝ} {A : ℝ}

/-- The chemical potential identity at a fixed time. -/
theorem rate_eq (hyp : Hyp V W KV KW) (h : LinMild ρ₀ ρ N A) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) {T K : ℝ} (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫ x, (entGp δ (heatT ε (ρ u) x) + V x) * forcing (ρ := ρ) (N := N) ε u x) +
      ∫ p, W p.1 p.2 * (forcing (ρ := ρ) (N := N) ε u p.1 * heatT ε (ρ u) p.2) ∂(volume.prod volume) =
      -epsRate V W δ ε (ρ u) (N u) := by
  set φ := heatT ε (ρ u) with hφdef
  set Fo := forcing (ρ := ρ) (N := N) ε u with hFo
  have hρu : Integrable (ρ u) (haar d) := appA_integrable_of_abs_le' (h.measurable_section u) (hK u hu)
  have hφ : IsSmoothT φ := isSmoothT_heatT hε hρu
  have hφc : Continuous φ := continuous_of_isSmoothT hφ
  have hφi : Integrable φ (haar d) := (memLp_of_continuous hφc 2).integrable one_le_two
  set ψ : Fin d → Torus d → ℝ := fun j => heatT ε (fun z => N u z j)
  have hψ : ∀ j, IsSmoothT (ψ j) := fun j => isSmoothT_heatT hε
    (appA_integrable_of_abs_le' (h.measurable_sectionN u j) fun z => h.abs_N_le hK hu z j)
  obtain ⟨MV, hMV⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_V.continuousOn
  have hVb : ∀ x, |V x| ≤ MV := fun x => by simpa [Real.norm_eq_abs] using hMV x (mem_univ _)
  obtain ⟨MW, hMW⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_W.continuousOn
  have hWb : ∀ x y, |W x y| ≤ MW := fun x y => by
    simpa [Real.norm_eq_abs] using hMW (x, y) (mem_univ _)
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hVg := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hCg := isWeakGrad_convDens' hyp hφi
  have hfg := hVg.add hCg
  set f : Torus d → ℝ := fun y => V y + convDens W φ y with hf
  have hfm : AEStronglyMeasurable f (haar d) :=
    hyp.continuous_V.aestronglyMeasurable.add hCg.aestronglyMeasurable_fun
  have hf2 : MemLp f 2 (haar d) := MemLp.of_bound hfm (MV + MW * ∫ y, |φ y| ∂haar d)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (add_le_add (hVb y) (abs_convDens_le hWb hφi y)))
  have hg2 : ∀ j, MemLp (fun y => lipGrad V y j + bForceL W φ y j) 2 (haar d) := fun j =>
    MemLp.of_bound ((appA_aestronglyMeasurable_grad hVg j).add (appA_aestronglyMeasurable_grad hCg j))
      (LV + Cb * ∫ y, |φ y| ∂haar d) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact (abs_add_le _ _).trans (add_le_add (hLV y j) (appA_abs_bForceL_le hCb hφi y j)))
  -- the forcing is the classical divergence
  have hFo : Fo =ᵐ[haar d] fun x => ∑ j, (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) := by
    filter_upwards [lapHeat_ae_eq hε (h.measurable_section u) (hK u hu),
      divHeatT_ae_eq hε (fun k => h.measurable_sectionN u k) (fun z k => h.abs_N_le hK hu z k)]
      with x h1 h2
    show lapHeat ε (ρ u) x + divHeatT ε (N u) x = _
    rw [h1, h2, Finset.sum_add_distrib]
  have hFoc : Continuous fun x => ∑ j, (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) :=
    continuous_finset_sum _ fun j _ => (continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_dpart hφ j) j)).add
      (continuous_of_isSmoothT (isSmoothT_dpart (hψ j) j))
  have hFo2 : MemLp Fo 2 (haar d) := (memLp_of_continuous hFoc 2).ae_eq hFo.symm
  -- the interaction term
  have hprod : ∫ p, W p.1 p.2 * (Fo p.1 * φ p.2) ∂(volume.prod volume) =
      ∫ x, convDens W φ x * Fo x ∂haar d := by
    have hWm : Measurable fun p : Torus d × Torus d => W p.1 p.2 := hyp.continuous_W.measurable
    have hFm : Measurable Fo := (h.measurable_forcing hε).comp measurable_prodMk_left
    obtain ⟨CF, hFb⟩ : ∃ CF, ∀ x, |Fo x| ≤ CF := ⟨_, fun x => h.abs_forcing_le hε hK hu x⟩
    obtain ⟨Mφ, hMφ⟩ := isCompact_univ.exists_bound_of_continuousOn hφc.continuousOn
    have hi : Integrable (fun p : Torus d × Torus d => W p.1 p.2 * (Fo p.1 * φ p.2))
        (volume.prod volume) := by
      refine integrable_of_abs_le_finite (B := MW * (CF * Mφ)) (hWm.mul ((hFm.comp measurable_fst).mul
        (hφc.measurable.comp measurable_snd))).aestronglyMeasurable fun p => ?_
      rw [abs_mul, abs_mul]
      have h1 := hMφ p.2 (mem_univ _); rw [Real.norm_eq_abs] at h1
      exact mul_le_mul (hWb _ _) (mul_le_mul (hFb p.1) h1 (abs_nonneg _)
        ((abs_nonneg _).trans (hFb p.1))) (by positivity) ((abs_nonneg _).trans (hWb p.1 p.2))
    rw [integral_prod _ hi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [convDens]
    rw [← integral_mul_const]
    congr 1; funext y; ring
  have hGφ : MemLp (fun x => entGp δ (φ x) + V x) 2 (haar d) := by
    obtain ⟨Mφ, hMφ⟩ := isCompact_univ.exists_bound_of_continuousOn
      ((continuous_entGp δ).comp hφc).continuousOn
    exact MemLp.of_bound (((continuous_entGp δ).comp hφc).aestronglyMeasurable.add
      hyp.continuous_V.aestronglyMeasurable) (Mφ + MV) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        refine (abs_add_le _ _).trans (add_le_add ?_ (hVb x))
        simpa [Real.norm_eq_abs] using hMφ x (mem_univ _))
  have hCf : MemLp (convDens W φ) 2 (haar d) := MemLp.of_bound hCg.aestronglyMeasurable_fun
    (MW * ∫ y, |φ y| ∂haar d) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_convDens_le hWb hφi y)
  rw [hprod, ← integral_add (f := fun x => (entGp δ (φ x) + V x) * Fo x)
    (g := fun x => convDens W φ x * Fo x) (hGφ.integrable_mul hFo2) (hCf.integrable_mul hFo2)]
  have e1 : ∫ x, ((entGp δ (φ x) + V x) * Fo x + convDens W φ x * Fo x) ∂haar d =
      ∫ x, (entGp δ (φ x) + f x) * ∑ j, (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) := by
    refine integral_congr_ae ?_
    filter_upwards [hFo] with x hx
    rw [← hx]; simp only [hf]; ring
  rw [e1, integral_mul_div_eq (hasDerivAt_entGp hδ) (continuous_entGpp hδ) hφ hψ hfg hf2 hg2]
  unfold epsRate
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1; funext x; ring

/-- **The free-energy identity at level `(ε, δ)`.** -/
theorem eps_identity (hyp : Hyp V W KV KW) (h : LinMild ρ₀ ρ N A) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    epsE V W δ ε (ρ t) = epsE V W δ ε ρ₀ - ∫ u in Ioc 0 t, epsRate V W δ ε (ρ u) (N u) := by
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨C, R, hC0, hR0, hFb, -, -, hφb⟩ := h.exists_version hε hK0 hK hT0
  obtain ⟨MV, hMV⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_V.continuousOn
  have hVb : ∀ x, |V x| ≤ MV := fun x => by simpa [Real.norm_eq_abs] using hMV x (mem_univ _)
  have hMV0 : 0 ≤ MV := (abs_nonneg _).trans (hVb 0)
  obtain ⟨MW, hMW⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_W.continuousOn
  have hWb : ∀ x y, |W x y| ≤ MW := fun x y => by
    simpa [Real.norm_eq_abs] using hMW (x, y) (mem_univ _)
  have hMW0 : 0 ≤ MW := (abs_nonneg _).trans (hWb 0 0)
  have hWm : Measurable (Function.uncurry W) := hyp.continuous_W.measurable
  have hGb : ∀ R', ∃ M, 0 ≤ M ∧ ∀ (x : Torus d) r, |r| ≤ R' →
      |entG δ r + V x * r| ≤ M ∧ |entGp δ r + V x| ≤ M := fun R' => by
    obtain ⟨M1, hM10, hM1⟩ := exists_bound_on_Icc (continuous_entG hδ) R'
    obtain ⟨M2, hM20, hM2⟩ := exists_bound_on_Icc (continuous_entGp δ) R'
    refine ⟨M1 + M2 + MV * |R'| + MV, by positivity, fun x r hr => ⟨?_, ?_⟩⟩
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have : |V x| * |r| ≤ MV * |R'| :=
        mul_le_mul (hVb x) (hr.trans (le_abs_self _)) (abs_nonneg _) hMV0
      linarith [hM1 r hr]
    · refine (abs_add_le _ _).trans ?_
      have := mul_nonneg hMV0 (abs_nonneg R')
      linarith [hM2 r hr, hVb x]
  have hE := h.energy_eq (G := fun x r => entG δ r + V x * r) (Gp := fun x r => entGp δ r + V x)
    (fun x r => by
      have := (hasDerivAt_entG hδ r).add ((hasDerivAt_id r).const_mul (V x))
      simp only [mul_one] at this
      exact this)
    (fun x => (continuous_entGp δ).add continuous_const)
    (((continuous_entG hδ).measurable.comp measurable_snd).add
      ((hyp.continuous_V.measurable.comp measurable_fst).mul measurable_snd))
    (((continuous_entGp δ).measurable.comp measurable_snd).add
      (hyp.continuous_V.measurable.comp measurable_fst)) hGb hε hK0 hK ht
  have hB := h.bilinear_eq (Wk := W) hWm hWb hyp.symm hε hK0 hK ht
  set Fo := forcing (ρ := ρ) (N := N) ε with hFo
  have hFm : Measurable (Function.uncurry Fo) := h.measurable_forcing hε
  set Af : ℝ → ℝ := fun u => ∫ x, (entGp δ (heatT ε (ρ u) x) + V x) * Fo u x with hAf
  set Bf : ℝ → ℝ := fun u =>
    ∫ p, W p.1 p.2 * (Fo u p.1 * heatT ε (ρ u) p.2) ∂(volume.prod volume) with hBf
  have hAm : Measurable Af := by
    have hm : Measurable fun p : ℝ × Torus d =>
        (entGp δ (heatT ε (ρ p.1) p.2) + V p.2) * Fo p.1 p.2 :=
      (((continuous_entGp δ).measurable.comp (measurable_heatT_family h.meas)).add
        (hyp.continuous_V.measurable.comp measurable_snd)).mul hFm
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hBm : Measurable Bf := by
    have hm : Measurable fun q : ℝ × (Torus d × Torus d) =>
        W q.2.1 q.2.2 * (Fo q.1 q.2.1 * heatT ε (ρ q.1) q.2.2) :=
      (hWm.comp measurable_snd).mul ((hFm.comp (measurable_fst.prodMk
        (measurable_fst.comp measurable_snd))).mul ((measurable_heatT_family h.meas).comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨MGp, hMGp0, hMGp⟩ := exists_bound_on_Icc (continuous_entGp δ) R
  have hAi : IntegrableOn Af (Ioc 0 t) := integrableOn_Ioc_of_abs_le hAm (M := (MGp + MV) * C)
    fun u hu => by
      have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
      refine abs_integral_le_of_abs_le fun x => ?_
      rw [abs_mul]
      exact mul_le_mul ((abs_add_le _ _).trans (add_le_add (hMGp _ (hφb u hu' x)) (hVb x)))
        (hFb u hu' x) (abs_nonneg _) (by positivity)
  have hBi : IntegrableOn Bf (Ioc 0 t) := integrableOn_Ioc_of_abs_le hBm (M := MW * (C * R))
    fun u hu => by
      have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
      refine abs_integral_le_of_abs_le fun p => ?_
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hWb _ _) (mul_le_mul (hFb u hu' _) (hφb u hu' _) (abs_nonneg _) hC0)
        (by positivity) hMW0
  have hR : ∫ u in Ioc 0 t, epsRate V W δ ε (ρ u) (N u) =
      -((∫ u in Ioc 0 t, Af u) + ∫ u in Ioc 0 t, Bf u) := by
    rw [← integral_add hAi hBi, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have := h.rate_eq hyp hδ hε hK ⟨hu.1.le, hu.2.trans ht.2⟩
    simp only [hAf, hBf]; linarith
  unfold epsE
  rw [hE, hB, hR]
  ring

end LinMild

end SharpLSI
