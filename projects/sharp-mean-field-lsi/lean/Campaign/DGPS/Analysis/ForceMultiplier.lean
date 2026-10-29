import DGPS.Foundations.WeakSobolev
import DGPS.Foundations.PeriodicSmoothing
open MeasureTheory
open scoped ContDiff

namespace DGPS.Analysis.ForceMultiplier

/-- Cauchy–Schwarz on the unit interval for `|W| |W'|`. -/
theorem integral_abs_mul_le (W W' : ℝ → ℝ) (hW : MemLp W 2 (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hW' : MemLp W' 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    ∫ s in (0:ℝ)..1, |W s| * |W' s| ≤
      Real.sqrt (∫ s in (0:ℝ)..1, W s ^ 2) * Real.sqrt (∫ s in (0:ℝ)..1, W' s ^ 2) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two)
    (f := fun s => |W s|) (g := fun s => |W' s|)
    (Filter.Eventually.of_forall fun s => abs_nonneg _) (Filter.Eventually.of_forall fun s => abs_nonneg _)
    (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact hW.abs) (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact hW'.abs)
  simp only [one_div, Real.rpow_two, sq_abs] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [one_div] using h


/-- Real-line periodic sup bound (Lemma A). -/
theorem sup_sq_le_of_periodic (W W' : ℝ → ℝ) (hper : Function.Periodic W 1)
    (hper' : Function.Periodic W' 1) (hWc : Continuous W)
    (hW' : MemLp W' 2 (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hftc : ∀ a b, W b ^ 2 - W a ^ 2 = ∫ s in a..b, 2 * W s * W' s) (s : ℝ) :
    W s ^ 2 ≤ (∫ t in (0:ℝ)..1, W t ^ 2) +
      2 * (Real.sqrt (∫ t in (0:ℝ)..1, W t ^ 2) * Real.sqrt (∫ t in (0:ℝ)..1, W' t ^ 2)) := by
  set m := ∫ t in (0:ℝ)..1, W t ^ 2 with hm
  have hWmem : MemLp W 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := W) (s := Set.Icc (0:ℝ) 1)
      hWc.continuousOn
    refine MemLp.of_bound hWc.aestronglyMeasurable C ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx)
  have hsq : IntegrableOn (fun t => W t ^ 2) (Set.Ioc (0:ℝ) 1) volume :=
    (hWc.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  obtain ⟨s₀, hs₀, hle⟩ := exists_le_setAverage (μ := volume) (s := Set.Ioc (0:ℝ) 1)
    (f := fun t => W t ^ 2) (by simp) (by simp) hsq
  have hav : ⨍ t in Set.Ioc (0:ℝ) 1, W t ^ 2 = m := by
    rw [setAverage_eq, hm, intervalIntegral.integral_of_le zero_le_one]; simp
  rw [hav] at hle
  -- the product is integrable
  have hprod : IntervalIntegrable (fun t => |2 * W t * W' t|) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have := ((hWmem.integrable_mul hW').norm.const_mul 2)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [abs_mul]; ring
  have hprodP : Function.Periodic (fun t => |2 * W t * W' t|) 1 := by
    intro t; simp [hper t, hper' t]
  have hprodI := hprodP.intervalIntegrable one_ne_zero (t := 0) (by rw [zero_add]; exact hprod)
  obtain ⟨s', hs', hss'⟩ := hper.exists_mem_Ico one_pos s s₀
  have h1 : W s' ^ 2 ≤ m + ∫ t in s₀..s₀ + 1, |2 * W t * W' t| := by
    have e := hftc s₀ s'
    have a1 : ∫ t in s₀..s', 2 * W t * W' t ≤ ∫ t in s₀..s', |2 * W t * W' t| :=
      (le_abs_self _).trans (intervalIntegral.abs_integral_le_integral_abs hs'.1)
    have a2 : ∫ t in s₀..s', |2 * W t * W' t| ≤ ∫ t in s₀..s₀ + 1, |2 * W t * W' t| :=
      intervalIntegral.integral_mono_interval le_rfl hs'.1 hs'.2.le
        (Filter.Eventually.of_forall fun t => abs_nonneg _) (hprodI _ _)
    linarith
  have h2 : ∫ t in s₀..s₀ + 1, |2 * W t * W' t| = ∫ t in (0:ℝ)..0 + 1, |2 * W t * W' t| :=
    hprodP.intervalIntegral_add_eq s₀ 0
  have h3 : ∫ t in (0:ℝ)..0 + 1, |2 * W t * W' t| =
      2 * ∫ t in (0:ℝ)..1, |W t| * |W' t| := by
    rw [zero_add, ← intervalIntegral.integral_const_mul]
    congr 1; ext t; simp [abs_mul]; ring
  have h4 := integral_abs_mul_le W W' hWmem hW'
  rw [hss']
  linarith


section slice
variable {N : ℕ}

theorem torusLift_add_int (v : Fin N → ℝ) (n : Fin N → ℤ) :
    torusLift (v + fun i => (n i : ℝ)) = torusLift v := by
  funext i
  simp only [SharpLSI.liftT, Pi.add_apply, AddCircle.coe_add]
  have : ((n i : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨n i, by simp⟩
  rw [this, add_zero]

theorem exists_secT_lift (v : Fin N → ℝ) :
    ∃ n : Fin N → ℤ, SharpLSI.secT (torusLift v) = v + fun i => (n i : ℝ) := by
  have h := SharpLSI.liftT_secT (torusLift v)
  have : ∀ i, ∃ k : ℤ, SharpLSI.secT (torusLift v) i = v i + k := by
    intro i
    have hi := congrFun h i
    simp only [SharpLSI.liftT] at hi
    have h0 : ((SharpLSI.secT (torusLift v) i - v i : ℝ) : AddCircle (1:ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).1 h0
    exact ⟨k, by simp at hk; linarith⟩
  choose n hn using this
  exact ⟨n, funext hn⟩


theorem fderiv_lift_add_int (ψ : Torus N → ℝ) (v : Fin N → ℝ) (n : Fin N → ℤ) :
    fderiv ℝ (ψ ∘ torusLift) (v + fun i => (n i : ℝ)) = fderiv ℝ (ψ ∘ torusLift) v := by
  have h : (ψ ∘ torusLift) = fun w => (ψ ∘ torusLift) (w + fun i => (n i : ℝ)) := by
    funext w; simp [Function.comp, torusLift_add_int]
  conv_rhs => rw [h]
  rw [fderiv_comp_add_right]

theorem coordPartial_torusLift (ψ : Torus N → ℝ) (j : Fin N) (v : Fin N → ℝ) :
    coordPartial j ψ (torusLift v) = fderiv ℝ (ψ ∘ torusLift) v (Pi.single j 1) := by
  obtain ⟨n, hn⟩ := exists_secT_lift v
  unfold coordPartial
  rw [hn, fderiv_lift_add_int]

theorem update_torusLift (X : Fin N → ℝ) (j : Fin N) (t : ℝ) :
    Function.update (torusLift X) j (t : AddCircle (1:ℝ)) = torusLift (Function.update X j t) := by
  funext i
  by_cases h : i = j
  · subst h; simp [SharpLSI.liftT]
  · simp [SharpLSI.liftT, h]

theorem memLp_two_Ioc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := f) (s := Set.Icc (0:ℝ) 1)
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx)

/-- Slice sup bound on `𝕋^N` for a smooth periodic `ψ` in coordinate `j`. -/
theorem slice_sup_sq_le {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) (j : Fin N) (x : Torus N) :
    ψ x ^ 2 ≤ (∫ s : AddCircle (1:ℝ), ψ (Function.update x j s) ^ 2) +
      2 * (Real.sqrt (∫ s : AddCircle (1:ℝ), ψ (Function.update x j s) ^ 2) *
        Real.sqrt (∫ s : AddCircle (1:ℝ), coordPartial j ψ (Function.update x j s) ^ 2)) := by
  set X := SharpLSI.secT x with hX
  have hlX : torusLift X = x := SharpLSI.liftT_secT x
  set Ψ : (Fin N → ℝ) → ℝ := ψ ∘ torusLift with hΨ
  have hΨs : ContDiff ℝ ∞ Ψ := hψ
  have hΨd : Differentiable ℝ Ψ := hΨs.differentiable (by simp)
  have hΨ1 : Continuous (fderiv ℝ Ψ) := hΨs.continuous_fderiv (by simp)
  set γ : ℝ → (Fin N → ℝ) := fun t => Function.update X j t with hγ
  have hγc : Continuous γ := (contDiff_update (𝕜 := ℝ) ∞ X j).continuous
  have hW : ∀ t : ℝ, ψ (Function.update x j (t : AddCircle (1:ℝ))) = Ψ (γ t) := by
    intro t; rw [← hlX, update_torusLift]; rfl
  have hW' : ∀ t : ℝ, coordPartial j ψ (Function.update x j (t : AddCircle (1:ℝ))) =
      fderiv ℝ Ψ (γ t) (Pi.single j 1) := by
    intro t; rw [← hlX, update_torusLift, coordPartial_torusLift]
  have hder : ∀ t, HasDerivAt (fun t => Ψ (γ t)) (fderiv ℝ Ψ (γ t) (Pi.single j 1)) t := by
    intro t
    exact (hΨd (γ t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update X j t)
  have hcW : Continuous (fun t => Ψ (γ t)) := hΨd.continuous.comp hγc
  have hcW' : Continuous (fun t => fderiv ℝ Ψ (γ t) (Pi.single j 1)) :=
    (hΨ1.comp hγc).clm_apply continuous_const
  have hper : ∀ t : ℝ, ((t + 1 : ℝ) : AddCircle (1:ℝ)) = (t : AddCircle (1:ℝ)) := by
    intro t; rw [AddCircle.coe_add]; simp
  have hperW : Function.Periodic (fun t => Ψ (γ t)) 1 := by
    intro t; simp only [← hW, hper]
  have hperW' : Function.Periodic (fun t => fderiv ℝ Ψ (γ t) (Pi.single j 1)) 1 := by
    intro t; simp only [← hW', hper]
  have key := sup_sq_le_of_periodic (fun t => Ψ (γ t)) (fun t => fderiv ℝ Ψ (γ t) (Pi.single j 1))
    hperW hperW' hcW (memLp_two_Ioc_of_continuous hcW') (by
      intro a b
      have h2 : ∀ t, HasDerivAt (fun t => Ψ (γ t) ^ 2)
          (2 * Ψ (γ t) * fderiv ℝ Ψ (γ t) (Pi.single j 1)) t := by
        intro t
        simpa [pow_one] using (hder t).fun_pow 2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h2 t)
        ((continuous_const.mul hcW |>.mul hcW').intervalIntegrable _ _)])
    (X j)
  have hAe : ∫ t in (0:ℝ)..1, Ψ (γ t) ^ 2 = ∫ s : AddCircle (1:ℝ), ψ (Function.update x j s) ^ 2 := by
    have := AddCircle.intervalIntegral_preimage (1:ℝ) 0
      (fun s : AddCircle (1:ℝ) => ψ (Function.update x j s) ^ 2)
    rw [zero_add] at this
    rw [← this]; simp only [hW]
  have hBe : ∫ t in (0:ℝ)..1, fderiv ℝ Ψ (γ t) (Pi.single j 1) ^ 2 =
      ∫ s : AddCircle (1:ℝ), coordPartial j ψ (Function.update x j s) ^ 2 := by
    have := AddCircle.intervalIntegral_preimage (1:ℝ) 0
      (fun s : AddCircle (1:ℝ) => coordPartial j ψ (Function.update x j s) ^ 2)
    rw [zero_add] at this
    rw [← this]; simp only [hW']
  have hxj : ψ x = Ψ (γ (X j)) := by
    rw [← hW, hX]
    have : ((SharpLSI.secT x j : ℝ) : AddCircle (1:ℝ)) = x j := congrFun (SharpLSI.liftT_secT x) j
    rw [this, Function.update_eq_self]
  rw [hAe, hBe] at key
  rw [hxj]; exact key


theorem smooth_eq_comp_secT {ψ : Torus N → ℝ} (x : Torus N) :
    ψ x = (ψ ∘ torusLift) (SharpLSI.secT x) := by
  simp [Function.comp, SharpLSI.liftT_secT]

theorem measurable_of_smooth {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) : Measurable ψ := by
  have : ψ = (ψ ∘ torusLift) ∘ SharpLSI.secT := by
    funext x; exact smooth_eq_comp_secT x
  rw [this]
  exact (hψ.continuous).measurable.comp SharpLSI.measurable_secT

theorem measurable_coordPartial {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) (j : Fin N) :
    Measurable (coordPartial j ψ) := by
  have h1 : Continuous (fderiv ℝ (ψ ∘ torusLift)) := (hψ : ContDiff ℝ ∞ (ψ ∘ torusLift)).continuous_fderiv (by simp)
  have : coordPartial j ψ = (fun v => fderiv ℝ (ψ ∘ torusLift) v (Pi.single j 1)) ∘ SharpLSI.secT := by
    funext x; rfl
  rw [this]
  exact ((h1.clm_apply continuous_const).measurable).comp SharpLSI.measurable_secT

theorem exists_bound_smooth {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) :
    ∃ C, ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin N → ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := ψ ∘ torusLift) hψ.continuous.continuousOn
  refine ⟨C, fun x => ?_⟩
  rw [smooth_eq_comp_secT (ψ := ψ) x]
  simpa using hC _ (DGPS.secT_mem_Icc x)

theorem exists_bound_coordPartial {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) (j : Fin N) :
    ∃ C, ∀ x, |coordPartial j ψ x| ≤ C := by
  have h1 : Continuous (fderiv ℝ (ψ ∘ torusLift)) := (hψ : ContDiff ℝ ∞ (ψ ∘ torusLift)).continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin N → ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun v => fderiv ℝ (ψ ∘ torusLift) v (Pi.single j 1))
    (h1.clm_apply continuous_const).continuousOn
  refine ⟨C, fun x => ?_⟩
  have := hC _ (DGPS.secT_mem_Icc x)
  simpa [coordPartial] using this


end slice

section cs
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_sqrt_mul_sqrt_le (a b : X → ℝ) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (ha : Measurable a) (hb : Measurable b) (hai : Integrable a μ) (hbi : Integrable b μ) :
    ∫ x, Real.sqrt (a x) * Real.sqrt (b x) ∂μ ≤
      Real.sqrt (∫ x, a x ∂μ) * Real.sqrt (∫ x, b x ∂μ) := by
  have h1 : MemLp (fun x => Real.sqrt (a x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq ha.sqrt.aestronglyMeasurable]
    simpa [Real.sq_sqrt (ha0 _)] using hai
  have h2 : MemLp (fun x => Real.sqrt (b x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hb.sqrt.aestronglyMeasurable]
    simpa [Real.sq_sqrt (hb0 _)] using hbi
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two)
    (f := fun x => Real.sqrt (a x)) (g := fun x => Real.sqrt (b x))
    (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact h1)
    (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact h2)
  simp only [one_div, Real.rpow_two, Real.sq_sqrt (ha0 _), Real.sq_sqrt (hb0 _)] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [one_div] using h

end cs

section part2
variable {n : ℕ}

theorem integral_slice (j : Fin (n+1)) {f : Torus (n+1) → ℝ} (hf : Integrable f (haar (n+1))) :
    ∫ x, f x ∂haar (n+1) =
      ∫ y : Fin n → AddCircle (1:ℝ), ∫ s : AddCircle (1:ℝ), f (j.insertNth s y) := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => AddCircle (1:ℝ)) j).symm
  have hint : Integrable (fun p : AddCircle (1:ℝ) × (Fin n → AddCircle (1:ℝ)) =>
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => AddCircle (1:ℝ)) j).symm p))
      (volume.prod volume) := by
    exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hf
  rw [← hmp.integral_comp' (g := f)]
  rw [Measure.volume_eq_prod, integral_prod_symm _ hint]
  rfl



theorem lintegral_circle_sq (g : Torus 1 → Tangent 1) (hg : MemLp g 2 (haar 1)) :
    ∫⁻ s : AddCircle (1:ℝ), ENNReal.ofReal (‖g (fun _ => s)‖ ^ 2) =
      ENNReal.ofReal (∫ t, ‖g t‖ ^ 2 ∂haar 1) := by
  have hi : Integrable (fun t => ‖g t‖ ^ 2) (haar 1) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun t => by positivity)]
  have hmp := measurePreserving_funUnique (volume : Measure (AddCircle (1:ℝ))) (Fin 1)
  have := hmp.lintegral_comp_emb (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ))).measurableEmbedding
    (fun s => ENNReal.ofReal (‖g (fun _ => s)‖ ^ 2))
  rw [← this]
  show _ = ∫⁻ t, ENNReal.ofReal (‖g t‖ ^ 2) ∂(Measure.pi fun _ : Fin 1 => (volume : Measure (AddCircle (1:ℝ))))
  congr 1
  funext t
  have : (fun _ : Fin 1 => (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ))) t) = t := by
    funext i; simp [MeasurableEquiv.funUnique, Subsingleton.elim i default]
  rw [this]

end part2

theorem slice_estimate_succ {n : ℕ} {g : Torus 1 → Tangent 1} (hg : MemLp g 2 (haar 1))
    {ψ : Torus (n+1) → ℝ} (hψ : IsSmoothPeriodic ψ) (i j : Fin (n+1)) (hij : i ≠ j) :
    ∫ x, ‖g (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar (n+1) ≤
      (∫ t, ‖g t‖ ^ 2 ∂haar 1) *
        ((∫ x, ψ x ^ 2 ∂haar (n+1)) +
          2 * (Real.sqrt (∫ x, ψ x ^ 2 ∂haar (n+1)) *
            Real.sqrt (∫ x, coordPartial j ψ x ^ 2 ∂haar (n+1)))) := by
  obtain ⟨C, hC⟩ := exists_bound_smooth hψ
  obtain ⟨D, hD⟩ := exists_bound_coordPartial hψ j
  have hψm := measurable_of_smooth hψ
  have hdm := measurable_coordPartial hψ j
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => AddCircle (1:ℝ)) j with he
  have hmp : MeasurePreserving e (haar (n+1)) (volume.prod volume) := by
    exact volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => AddCircle (1:ℝ)) j
  set A : (Fin n → AddCircle (1:ℝ)) → ℝ := fun y => ∫ s : AddCircle (1:ℝ), ψ (j.insertNth s y) ^ 2
    with hA
  set B : (Fin n → AddCircle (1:ℝ)) → ℝ :=
    fun y => ∫ s : AddCircle (1:ℝ), coordPartial j ψ (j.insertNth s y) ^ 2 with hB
  have hA0 : ∀ y, 0 ≤ A y := fun y => integral_nonneg fun s => sq_nonneg _
  have hB0 : ∀ y, 0 ≤ B y := fun y => integral_nonneg fun s => sq_nonneg _
  have hAle : ∀ y, A y ≤ C ^ 2 := by
    intro y
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg _)
      (integrable_const (C ^ 2)) (Filter.Eventually.of_forall fun s => ?_)).trans (by simp)
    have := hC (j.insertNth s y)
    nlinarith [abs_nonneg (ψ (j.insertNth s y)), sq_abs (ψ (j.insertNth s y))]
  have hBle : ∀ y, B y ≤ D ^ 2 := by
    intro y
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg _)
      (integrable_const (D ^ 2)) (Filter.Eventually.of_forall fun s => ?_)).trans (by simp)
    have := hD (j.insertNth s y)
    nlinarith [abs_nonneg (coordPartial j ψ (j.insertNth s y)), sq_abs (coordPartial j ψ (j.insertNth s y))]
  -- measurability of the slice functions
  have hmeas_e : Measurable (fun p : AddCircle (1:ℝ) × (Fin n → AddCircle (1:ℝ)) =>
      j.insertNth (α := fun _ => AddCircle (1:ℝ)) p.1 p.2) :=
    e.symm.measurable
  have hAm : Measurable A := by
    have : StronglyMeasurable (Function.uncurry fun (s : AddCircle (1:ℝ)) (y : Fin n → AddCircle (1:ℝ)) =>
        ψ (j.insertNth s y) ^ 2) :=
      ((hψm.comp hmeas_e).pow_const 2).stronglyMeasurable
    exact (this.integral_prod_left (μ := volume)).measurable
  have hBm : Measurable B := by
    have : StronglyMeasurable (Function.uncurry fun (s : AddCircle (1:ℝ)) (y : Fin n → AddCircle (1:ℝ)) =>
        coordPartial j ψ (j.insertNth s y) ^ 2) :=
      ((hdm.comp hmeas_e).pow_const 2).stronglyMeasurable
    exact (this.integral_prod_left (μ := volume)).measurable
  have hAi : Integrable A := Integrable.of_bound hAm.aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hA0 y)]; exact hAle y)
  have hBi : Integrable B := Integrable.of_bound hBm.aestronglyMeasurable (D ^ 2)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hB0 y)]; exact hBle y)
  -- Fubini
  have hψ2i : Integrable (fun x => ψ x ^ 2) (haar (n+1)) := Integrable.of_bound
    (hψm.pow_const 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun x => by
      have := hC x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (ψ x), sq_abs (ψ x)])
  have hd2i : Integrable (fun x => coordPartial j ψ x ^ 2) (haar (n+1)) := Integrable.of_bound
    (hdm.pow_const 2).aestronglyMeasurable (D ^ 2) (Filter.Eventually.of_forall fun x => by
      have := hD x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (coordPartial j ψ x), sq_abs (coordPartial j ψ x)])
  have hintA : ∫ x, ψ x ^ 2 ∂haar (n+1) = ∫ y, A y := integral_slice j hψ2i
  have hintB : ∫ x, coordPartial j ψ x ^ 2 ∂haar (n+1) = ∫ y, B y := integral_slice j hd2i
  set S : (Fin n → AddCircle (1:ℝ)) → ℝ := fun y => A y + 2 * (Real.sqrt (A y) * Real.sqrt (B y))
    with hS
  have hS0 : ∀ y, 0 ≤ S y := fun y => by
    have := hA0 y
    simp only [hS]; positivity
  have hkey : ∀ y s, ψ (j.insertNth s y) ^ 2 ≤ S y := by
    intro y s
    have := slice_sup_sq_le hψ j (j.insertNth s y)
    simp only [Fin.update_insertNth] at this
    exact this
  have hSqm : Measurable (fun y => Real.sqrt (A y) * Real.sqrt (B y)) := hAm.sqrt.mul hBm.sqrt
  have hSqi : Integrable (fun y => Real.sqrt (A y) * Real.sqrt (B y)) := by
    refine (hAi.add hBi).mono' hSqm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have h1 := Real.sq_sqrt (hA0 y)
    have h2 := Real.sq_sqrt (hB0 y)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.sqrt (A y) - Real.sqrt (B y))]
  have hSi : Integrable S := hAi.add (hSqi.const_mul 2)
  have hSint : ∫ y, S y ≤ (∫ y, A y) + 2 * (Real.sqrt (∫ y, A y) * Real.sqrt (∫ y, B y)) := by
    have hcs := integral_sqrt_mul_sqrt_le (μ := volume) A B hA0 hB0 hAm hBm hAi hBi
    have : ∫ y, S y = (∫ y, A y) + 2 * ∫ y, Real.sqrt (A y) * Real.sqrt (B y) := by
      simp only [hS]
      rw [integral_add hAi (hSqi.const_mul 2), integral_const_mul]
    rw [this]; linarith
  set β2 := ∫ t, ‖g t‖ ^ 2 ∂haar 1 with hβ2
  have hβ2nn : 0 ≤ β2 := integral_nonneg fun t => by positivity
  have hAint0 : 0 ≤ ∫ y, A y := integral_nonneg hA0
  rw [hintA, hintB]
  have hRHSnn : 0 ≤ β2 * ((∫ y, A y) + 2 * (Real.sqrt (∫ y, A y) * Real.sqrt (∫ y, B y))) :=
    mul_nonneg hβ2nn (by positivity)
  by_cases hFm : AEStronglyMeasurable (fun x : Torus (n+1) => ‖g (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2)
      (haar (n+1))
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity) hFm]
    refine ENNReal.toReal_le_of_le_ofReal hRHSnn ?_
    have hae : AEMeasurable (fun p : AddCircle (1:ℝ) × (Fin n → AddCircle (1:ℝ)) =>
        ENNReal.ofReal (‖g (fun _ => (e.symm p) i - (e.symm p) j)‖ ^ 2 * ψ (e.symm p) ^ 2))
        (volume.prod volume) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (hFm.comp_measurePreserving (hmp.symm e)).aemeasurable
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    have hinner : ∀ y : Fin n → AddCircle (1:ℝ),
        ∫⁻ s : AddCircle (1:ℝ), ENNReal.ofReal (‖g (fun _ => (j.insertNth s y : Fin (n+1) → AddCircle (1:ℝ)) i -
          (j.insertNth s y : Fin (n+1) → AddCircle (1:ℝ)) j)‖ ^ 2 * ψ (j.insertNth s y) ^ 2) ≤
        ENNReal.ofReal (S y) * ENNReal.ofReal β2 := by
      intro y
      have hxi : ∀ s : AddCircle (1:ℝ), (j.insertNth s y : Fin (n+1) → AddCircle (1:ℝ)) i = y k := by
        intro s; rw [← hk]; simp [Fin.insertNth_apply_succAbove]
      have hxj : ∀ s : AddCircle (1:ℝ), (j.insertNth s y : Fin (n+1) → AddCircle (1:ℝ)) j = s := by
        intro s; simp
      calc _ ≤ ∫⁻ s : AddCircle (1:ℝ), ENNReal.ofReal (‖g (fun _ => y k - s)‖ ^ 2) * ENNReal.ofReal (S y) := by
            refine lintegral_mono fun s => ?_
            rw [hxi, hxj, ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hkey y s) (by positivity))
        _ = (∫⁻ s : AddCircle (1:ℝ), ENNReal.ofReal (‖g (fun _ => y k - s)‖ ^ 2)) * ENNReal.ofReal (S y) :=
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal β2 * ENNReal.ofReal (S y) := by
            rw [lintegral_sub_left_eq_self (μ := (volume : Measure (AddCircle (1:ℝ))))
              (fun t => ENNReal.ofReal (‖g (fun _ => t)‖ ^ 2)) (y k), lintegral_circle_sq g hg]
        _ = _ := mul_comm _ _
    calc ∫⁻ x, ENNReal.ofReal (‖g (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2) ∂haar (n+1)
        = ∫⁻ p, ENNReal.ofReal (‖g (fun _ => (e.symm p) i - (e.symm p) j)‖ ^ 2 * ψ (e.symm p) ^ 2)
            ∂(volume.prod volume) := by
          rw [← hmp.lintegral_comp_emb e.measurableEmbedding
            (fun p => ENNReal.ofReal (‖g (fun _ => (e.symm p) i - (e.symm p) j)‖ ^ 2 * ψ (e.symm p) ^ 2))]
          simp
      _ = ∫⁻ y : Fin n → AddCircle (1:ℝ), ∫⁻ s : AddCircle (1:ℝ),
            ENNReal.ofReal (‖g (fun _ => (j.insertNth s y : Fin (n+1) → AddCircle (1:ℝ)) i -
              (j.insertNth s y : Fin (n+1) → AddCircle (1:ℝ)) j)‖ ^ 2 * ψ (j.insertNth s y) ^ 2) := by
          rw [lintegral_prod_symm _ hae]; rfl
      _ ≤ ∫⁻ y : Fin n → AddCircle (1:ℝ), ENNReal.ofReal (S y) * ENNReal.ofReal β2 :=
          lintegral_mono hinner
      _ = (∫⁻ y : Fin n → AddCircle (1:ℝ), ENNReal.ofReal (S y)) * ENNReal.ofReal β2 :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (∫ y, S y) * ENNReal.ofReal β2 := by
          rw [ofReal_integral_eq_lintegral_ofReal hSi (Filter.Eventually.of_forall hS0)]
      _ ≤ ENNReal.ofReal ((∫ y, A y) + 2 * (Real.sqrt (∫ y, A y) * Real.sqrt (∫ y, B y))) *
            ENNReal.ofReal β2 := by
          gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  · rw [integral_non_aestronglyMeasurable hFm]; exact hRHSnn


section part1

open Filter Topology

theorem integral_sq_eq_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : ∫ x, f x ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
  have h1 : ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
  rw [h1, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]; simp [sq]

theorem tendsto_integral_sq_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (hF : MemLp F 2 μ)
    (h : Tendsto (fun k => eLpNorm (f k - F) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x ^ 2 ∂μ) atTop (𝓝 (∫ x, F x ^ 2 ∂μ)) := by
  have : Fact ((1:ENNReal) ≤ 2) := ⟨one_le_two⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).2 h
  have h2 := (this.norm).pow 2
  simp_rw [← integral_sq_eq_norm_sq] at h2
  exact h2

theorem integral_circle (f : Torus 1 → ℝ) :
    ∫ s : AddCircle (1:ℝ), f (fun _ => s) = ∫ t, f t ∂haar 1 := by
  have hmp := measurePreserving_funUnique (volume : Measure (AddCircle (1:ℝ))) (Fin 1)
  have := hmp.integral_comp' (g := fun s => f (fun _ => s))
  have e : ∀ t : Torus 1, (fun _ : Fin 1 => (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ))) t) = t := by
    intro t; funext i; simp [MeasurableEquiv.funUnique, Subsingleton.elim i default]
  simp_rw [e] at this
  rw [← this]
  rfl

theorem update_zero_eq (x : Torus 1) (s : AddCircle (1:ℝ)) :
    Function.update x 0 s = fun _ => s := by
  funext i; simp [Subsingleton.elim i 0]

/-- Part 1 for smooth periodic `z` on the circle. -/
theorem smooth_sup_sq_le {z : Torus 1 → ℝ} (hz : IsSmoothPeriodic z) (x : Torus 1) :
    z x ^ 2 ≤ (∫ t, z t ^ 2 ∂haar 1) +
      2 * (Real.sqrt (∫ t, z t ^ 2 ∂haar 1) *
        Real.sqrt (∫ t, coordPartial 0 z t ^ 2 ∂haar 1)) := by
  have h := slice_sup_sq_le hz 0 x
  simp_rw [update_zero_eq] at h
  rw [integral_circle (fun t => z t ^ 2), integral_circle (fun t => coordPartial 0 z t ^ 2)] at h
  exact h

theorem memLp_two_of_smooth {d : ℕ} {z : Torus d → ℝ} (hz : IsSmoothPeriodic z) : MemLp z 2 (haar d) :=
  hz.memLp_top.mono_exponent le_top

theorem memLp_two_coordPartial {d : ℕ} {z : Torus d → ℝ} (hz : IsSmoothPeriodic z) (j : Fin d) :
    MemLp (coordPartial j z) 2 (haar d) :=
  (hz.memLp_top_coordPartial j).mono_exponent le_top

theorem integral_norm_sq_one (g : Torus 1 → Tangent 1) :
    ∫ t, ‖g t‖ ^ 2 ∂haar 1 = ∫ t, g t 0 ^ 2 ∂haar 1 := by
  congr 1; funext t
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp

/-- Part 1, `H¹` version: if `z` has weak gradient `g` and is the `L²`-limit of smooth periodic
functions whose derivatives converge in `L²` to `g`, then the sup bound holds a.e. -/
theorem sup_sq_le_of_approx {z : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (hz : IsWeakGradient z g)
    (zs : ℕ → Torus 1 → ℝ) (hs : ∀ k, IsSmoothPeriodic (zs k))
    (h0 : Filter.Tendsto (fun k => eLpNorm (zs k - z) 2 (haar 1)) Filter.atTop (nhds 0))
    (h1 : Filter.Tendsto (fun k => eLpNorm (coordPartial 0 (zs k) - fun t => g t 0) 2 (haar 1))
      Filter.atTop (nhds 0)) :
    ∀ᵐ x ∂haar 1, z x ^ 2 ≤ (∫ t, z t ^ 2 ∂haar 1) +
      2 * (Real.sqrt (∫ t, z t ^ 2 ∂haar 1) * Real.sqrt (∫ t, ‖g t‖ ^ 2 ∂haar 1)) := by
  have hG := memLp_coord hz.memLp_grad 0
  have T1 := tendsto_integral_sq_of_eLpNorm (fun k => memLp_two_of_smooth (hs k)) hz.memLp h0
  have T2 := tendsto_integral_sq_of_eLpNorm (fun k => memLp_two_coordPartial (hs k) 0) hG h1
  rw [integral_norm_sq_one]
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (μ := haar 1) (p := 2) (by norm_num) h0
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hae] with x hx
  have hx2 : Filter.Tendsto (fun i => zs (ns i) x ^ 2) Filter.atTop (nhds (z x ^ 2)) :=
    (hx.pow 2)
  have T1' := T1.comp hns.tendsto_atTop
  have T2' := T2.comp hns.tendsto_atTop
  have R : Filter.Tendsto (fun i =>
      (∫ t, zs (ns i) t ^ 2 ∂haar 1) + 2 * (Real.sqrt (∫ t, zs (ns i) t ^ 2 ∂haar 1) *
        Real.sqrt (∫ t, coordPartial 0 (zs (ns i)) t ^ 2 ∂haar 1))) Filter.atTop
      (nhds ((∫ t, z t ^ 2 ∂haar 1) + 2 * (Real.sqrt (∫ t, z t ^ 2 ∂haar 1) *
        Real.sqrt (∫ t, g t 0 ^ 2 ∂haar 1)))) :=
    T1'.add ((T1'.sqrt.mul T2'.sqrt).const_mul 2)
  exact le_of_tendsto_of_tendsto hx2 R (Filter.Eventually.of_forall fun i =>
    smooth_sup_sq_le (hs (ns i)) x)

end part1


section final

/-- `z` is approximated in `H¹(𝕋)` by smooth periodic functions (the shape consumed by
`sup_sq_le_of_approx`); it holds for every weak-gradient pair by FOU002. -/
def HasSmoothApprox (z : Torus 1 → ℝ) (g : Torus 1 → Tangent 1) : Prop :=
  ∃ zs : ℕ → Torus 1 → ℝ, (∀ k, IsSmoothPeriodic (zs k)) ∧
    Filter.Tendsto (fun k => eLpNorm (zs k - z) 2 (haar 1)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => eLpNorm (coordPartial 0 (zs k) - fun t => g t 0) 2 (haar 1))
      Filter.atTop (nhds 0)

theorem hasSmoothApprox {z : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (hz : IsWeakGradient z g) :
    HasSmoothApprox z g := by
  obtain ⟨v, hv, -, h0, h1⟩ := exists_smooth_tendsto_H1 hz
  exact ⟨v, hv, h0, h1 0⟩

/-- Part 2 of H1021 for a general number `N` of coordinates and any `L²` gradient `g`. -/
theorem slice_estimate {N : ℕ} {g : Torus 1 → Tangent 1} (hg : MemLp g 2 (haar 1))
    {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) (i j : Fin N) (hij : i ≠ j) :
    ∫ x, ‖g (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N ≤
      (∫ t, ‖g t‖ ^ 2 ∂haar 1) *
        ((∫ x, ψ x ^ 2 ∂haar N) +
          2 * (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N) *
            Real.sqrt (∫ x, coordPartial j ψ x ^ 2 ∂haar N))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i.pos; omega⟩
  exact slice_estimate_succ hg hψ i j hij

/-- H1021, circle slice sup norm.
(1) For real `z ∈ H¹(𝕋)` with weak derivative `g`:
`‖z‖∞² ≤ ‖z‖₂² + 2‖z‖₂‖z′‖₂`, as an essential-sup bound (`z² ≤ …` a.e.).
(2) For `Q ∈ H¹(𝕋)`, `β = ‖Q′‖₂`, smooth `ψ` on `𝕋^N`, `i ≠ j`, `u = ‖ψ‖₂`:
`∫ |Q′(x_i - x_j)|² ψ² dm^N ≤ β² (u² + 2u‖∂ⱼψ‖₂)`. -/
theorem circle_slice_sup_norm :
    (∀ (z : Torus 1 → ℝ) (g : Torus 1 → Tangent 1), IsWeakGradient z g →
      ∀ᵐ x ∂haar 1, z x ^ 2 ≤ (Real.sqrt (∫ t, z t ^ 2 ∂haar 1)) ^ 2 +
        2 * (Real.sqrt (∫ t, z t ^ 2 ∂haar 1) * Real.sqrt (∫ t, ‖g t‖ ^ 2 ∂haar 1))) ∧
    (∀ (N : ℕ) (Q : Torus 1 → ℝ) (hQ : MemH1 Q) (ψ : Torus N → ℝ), IsSmoothPeriodic ψ →
      ∀ i j : Fin N, i ≠ j →
        ∫ x, ‖weakGradient Q hQ (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N ≤
          (Real.sqrt (∫ t, ‖weakGradient Q hQ t‖ ^ 2 ∂haar 1)) ^ 2 *
            ((Real.sqrt (∫ x, ψ x ^ 2 ∂haar N)) ^ 2 +
              2 * (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N) *
                Real.sqrt (∫ x, coordPartial j ψ x ^ 2 ∂haar N)))) := by
  refine ⟨fun z g hz => ?_, fun N Q hQ ψ hψ i j hij => ?_⟩
  · obtain ⟨zs, hs, h0, h1⟩ := hasSmoothApprox hz
    have := sup_sq_le_of_approx hz zs hs h0 h1
    rwa [Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]
  · have h := slice_estimate (isWeakGradient_weakGradient hQ).memLp_grad hψ i j hij
    rwa [Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _),
      Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]

end final

section repeated

theorem sum_integral_coordPartial_sq {N : ℕ} {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) :
    ∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N = ∑ j, ∫ x, coordPartial j ψ x ^ 2 ∂haar N := by
  have hint : ∀ j, Integrable (fun x => coordPartial j ψ x ^ 2) (haar N) := fun j =>
    (memLp_two_coordPartial hψ j).integrable_sq
  rw [← integral_finsetSum _ (fun j _ => hint j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [smoothGrad, EuclideanSpace.norm_sq_eq]

/-- H1022, repeated label force estimate. For `N ≥ 2`, `β = ‖Q′‖₂`, `u = ‖ψ‖₂`,
`v = ‖∇ψ‖₂`: `D = N⁻² ∑_{i≠j} ∫ |Q′(xᵢ - xⱼ)|² ψ² ≤ β² (u² + 2uv/√N)`. -/
theorem repeated_label_force_estimate (N : ℕ) (hN : 2 ≤ N) (Q : Torus 1 → ℝ) (hQ : MemH1 Q)
    (ψ : Torus N → ℝ) (hψ : IsSmoothPeriodic ψ) :
    ((N : ℝ) ^ 2)⁻¹ * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        ∫ x, ‖weakGradient Q hQ (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N ≤
      (Real.sqrt (∫ t, ‖weakGradient Q hQ t‖ ^ 2 ∂haar 1)) ^ 2 *
        ((Real.sqrt (∫ x, ψ x ^ 2 ∂haar N)) ^ 2 +
          2 * (Real.sqrt (∫ x, ψ x ^ 2 ∂haar N) *
            Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N)) / Real.sqrt N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hB0 : 0 ≤ ∫ t, ‖weakGradient Q hQ t‖ ^ 2 ∂haar 1 := integral_nonneg fun t => sq_nonneg _
  have hU0 : 0 ≤ ∫ x, ψ x ^ 2 ∂haar N := integral_nonneg fun t => sq_nonneg _
  rw [Real.sq_sqrt hB0, Real.sq_sqrt hU0]
  set B := ∫ t, ‖weakGradient Q hQ t‖ ^ 2 ∂haar 1 with hB
  set U := ∫ x, ψ x ^ 2 ∂haar N with hU
  set a : Fin N → ℝ := fun j => Real.sqrt (∫ x, coordPartial j ψ x ^ 2 ∂haar N) with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => Real.sqrt_nonneg _
  set v := Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N) with hv
  have hsum : ∑ j, a j ≤ Real.sqrt N * v := by
    have hsq : (∑ j, a j) ^ 2 ≤ (N : ℝ) * ∑ j, a j ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
      simpa using this
    have hsq2 : ∑ j, a j ^ 2 = v ^ 2 := by
      rw [hv, Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _),
        sum_integral_coordPartial_sq hψ]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)
    rw [hsq2] at hsq
    have hr : (Real.sqrt N * v) ^ 2 = N * v ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hNpos.le]
    exact abs_le_of_sq_le_sq' (by rw [hr]; exact hsq)
      (mul_nonneg hsN.le (Real.sqrt_nonneg _)) |>.2
  have hu : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hUu : Real.sqrt U ^ 2 = U := Real.sq_sqrt hU0
  have hterm : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i,
      ∫ x, ‖weakGradient Q hQ (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N ≤
      B * (N * U + 2 * (Real.sqrt U * (Real.sqrt N * v))) := by
    intro i
    have h1 : ∀ j ∈ Finset.univ.erase i,
        ∫ x, ‖weakGradient Q hQ (fun _ => x i - x j)‖ ^ 2 * ψ x ^ 2 ∂haar N ≤
          B * (U + 2 * (Real.sqrt U * a j)) := fun j hj =>
      slice_estimate (isWeakGradient_weakGradient hQ).memLp_grad hψ i j
        (Finset.ne_of_mem_erase hj).symm
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hsub : ∑ j ∈ Finset.univ.erase i, a j ≤ ∑ j, a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => ha0 j
    have hc : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le _ _
    refine mul_le_mul_of_nonneg_left ?_ hB0
    have := mul_le_mul_of_nonneg_left hc hU0
    have h2 := mul_le_mul_of_nonneg_left (hsub.trans hsum) hu
    nlinarith [mul_comm U (((N - 1 : ℕ) : ℝ))]
  have htot := (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hN2]
  refine htot.trans (le_of_eq ?_)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  generalize Real.sqrt N = s at hsq hsN ⊢
  rw [← hsq]
  field_simp

end repeated

section distinct

variable {N : ℕ}

/-- The function `x ↦ f (x_i - x_j)` on `𝕋^N`. -/
noncomputable def pairFun (f : Torus 1 → ℝ) (i j : Fin N) (x : Torus N) : ℝ :=
  f (fun _ => x i - x j)

theorem pairFun_comp_torusLift (f : Torus 1 → ℝ) (i j : Fin N) :
    pairFun f i j ∘ torusLift =
      (f ∘ torusLift) ∘ (fun v : Fin N → ℝ => fun _ : Fin 1 => v i - v j) := by
  funext v
  simp only [pairFun, Function.comp]
  congr 1

theorem isSmoothPeriodic_pairFun {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) (i j : Fin N) :
    IsSmoothPeriodic (pairFun f i j) := by
  unfold IsSmoothPeriodic
  rw [pairFun_comp_torusLift]
  refine ContDiff.comp hf ?_
  refine contDiff_pi.2 fun _ => ?_
  exact (contDiff_apply ℝ ℝ i).sub (contDiff_apply ℝ ℝ j)

theorem coordPartial_pairFun {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) (i j l : Fin N)
    (x : Torus N) :
    coordPartial l (pairFun f i j) x =
      ((if l = i then 1 else 0) - (if l = j then 1 else 0)) *
        coordPartial 0 f (fun _ => x i - x j) := by
  have hx : x = torusLift (SharpLSI.secT x) := (SharpLSI.liftT_secT x).symm
  set v := SharpLSI.secT x with hv
  have hxi : ∀ k, x k = ((v k : ℝ) : AddCircle (1:ℝ)) := fun k => by
    have := congrFun (SharpLSI.liftT_secT x) k
    simpa [SharpLSI.liftT] using this.symm
  rw [hx, coordPartial_torusLift, pairFun_comp_torusLift]
  let A : (Fin N → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi fun _ : Fin 1 =>
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i) - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j))
  have hA : (fun v : Fin N → ℝ => fun _ : Fin 1 => v i - v j) = A := by
    funext v k; simp [A]
  rw [hA]
  have hd : DifferentiableAt ℝ (f ∘ torusLift) (A v) :=
    (hf.differentiable (by simp)) _
  rw [fderiv_comp v hd A.differentiableAt, A.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h1 : A (Pi.single l 1) = ((if l = i then 1 else 0) - (if l = j then 1 else 0) : ℝ) • (Pi.single 0 1 : Fin 1 → ℝ) := by
    funext k
    have : k = 0 := Subsingleton.elim _ _
    subst this
    by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [A, h1, h2, Pi.single_apply, eq_comm]
  rw [h1, map_smul, smul_eq_mul]
  congr 1
  have h2 : (fun _ : Fin 1 => torusLift v i - torusLift v j) = torusLift (A v) := by
    funext k; simp [A, SharpLSI.liftT]
  rw [h2, coordPartial_torusLift]

theorem coordPartial_mul {v φ : Torus N → ℝ} (hv : IsSmoothPeriodic v)
    (hφ : IsSmoothPeriodic φ) (j : Fin N) (y : Torus N) :
    coordPartial j (fun x => v x * φ x) y = v y * coordPartial j φ y + coordPartial j v y * φ y := by
  have hv1 : DifferentiableAt ℝ (v ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
    (hv.differentiable (by simp)) _
  have hφ1 : DifferentiableAt ℝ (φ ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
    (hφ.differentiable (by simp)) _
  have : ((fun x => v x * φ x) ∘ SharpLSI.liftT) =
      fun x => (v ∘ SharpLSI.liftT) x * (φ ∘ SharpLSI.liftT) x := rfl
  unfold coordPartial
  rw [this, fderiv_fun_mul hv1 hφ1]
  simp only [add_apply, smul_apply, smul_eq_mul,
    Function.comp_apply, SharpLSI.liftT_secT]
  ring

theorem integrable_of_continuous' {f : Torus N → ℝ} (hf : Continuous f) : Integrable f (haar N) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem ibp_triple {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q) {ψ : Torus N → ℝ}
    (hψ : IsSmoothPeriodic ψ) {i j k : Fin N} (hij : i ≠ j) (hkj : k ≠ j) :
    ∫ x, ψ x ^ 2 * pairFun (coordPartial 0 Q) i j x * pairFun (coordPartial 0 Q) i k x ∂haar N =
      2 * ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i k x * ψ x * coordPartial j ψ x
        ∂haar N := by
  have hq := hQ.isSmoothPeriodic_coordPartial 0
  have hv := isSmoothPeriodic_pairFun hQ i j
  have hqik := isSmoothPeriodic_pairFun hq i k
  have hφ : IsSmoothPeriodic (fun x => ψ x * (ψ x * pairFun (coordPartial 0 Q) i k x)) :=
    hψ.mul (hψ.mul hqik)
  have h := integral_mul_coordPartial_of_smooth hv hφ j
  have hdq : ∀ x, coordPartial j (pairFun (coordPartial 0 Q) i k) x = 0 := by
    intro x
    rw [coordPartial_pairFun hq]
    simp [hij.symm, hkj.symm]
  have hdv : ∀ x, coordPartial j (pairFun Q i j) x = - pairFun (coordPartial 0 Q) i j x := by
    intro x
    rw [coordPartial_pairFun hQ]
    simp [hij.symm, pairFun]
  have hdφ : ∀ x, coordPartial j (fun x => ψ x * (ψ x * pairFun (coordPartial 0 Q) i k x)) x =
      2 * (ψ x * coordPartial j ψ x * pairFun (coordPartial 0 Q) i k x) := by
    intro x
    rw [coordPartial_mul hψ (hψ.mul hqik), coordPartial_mul hψ hqik, hdq]
    ring
  simp_rw [hdφ, hdv] at h
  have e1 : ∫ x, pairFun Q i j x * (2 * (ψ x * coordPartial j ψ x * pairFun (coordPartial 0 Q) i k x)) ∂haar N =
      2 * ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i k x * ψ x * coordPartial j ψ x ∂haar N := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [← e1, h, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring

theorem sq_sum_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) :
    (∑ j ∈ s, a j) ^ 2 = ∑ j ∈ s, a j ^ 2 + ∑ j ∈ s, ∑ k ∈ s.erase j, a j * a k := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.add_sum_erase s (fun k => a j * a k) hj, sq]

theorem integral_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → Torus N → ℝ}
    (hf : ∀ i, Continuous (f i)) :
    ∫ x, ∑ i ∈ s, f i x ∂haar N = ∑ i ∈ s, ∫ x, f i x ∂haar N :=
  integral_finsetSum s fun i _ => integrable_of_continuous' (hf i)

theorem distinct_identity_core {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q) {ψ : Torus N → ℝ}
    (hψ : IsSmoothPeriodic ψ) :
    ∫ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
        pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N -
      ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N =
    (2 / N) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase i,
          pairFun (coordPartial 0 Q) i k x) * ψ x * coordPartial j ψ x ∂haar N -
    (2 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i j x * ψ x * coordPartial j ψ x
          ∂haar N := by
  have hq := hQ.isSmoothPeriodic_coordPartial 0
  have hcQ : ∀ i j : Fin N, Continuous (pairFun Q i j) := fun i j =>
    (isSmoothPeriodic_pairFun hQ i j).continuous_torus
  have hcq : ∀ i j : Fin N, Continuous (pairFun (coordPartial 0 Q) i j) := fun i j =>
    (isSmoothPeriodic_pairFun hq i j).continuous_torus
  have hcψ : Continuous ψ := hψ.continuous_torus
  have hcd : ∀ j, Continuous (coordPartial j ψ) := fun j => hψ.continuous_coordPartial j
  set P : Fin N → Fin N → Torus N → ℝ := fun i j => pairFun (coordPartial 0 Q) i j with hP
  have hcP : ∀ i j, Continuous (P i j) := hcq
  set E : Fin N → Finset (Fin N) := fun i => Finset.univ.erase i with hE
  by_cases hN0 : N = 0
  · subst hN0
    simp
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  -- pointwise expansion
  have hpt : ∀ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ E i, P i j x)) ^ 2 =
      ((N : ℝ) ^ 2)⁻¹ * (∑ i, ∑ j ∈ E i, P i j x ^ 2 * ψ x ^ 2 +
        ∑ i, ∑ j ∈ E i, ∑ k ∈ (E i).erase j, ψ x ^ 2 * (P i j x * P i k x)) := by
    intro x
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := sq_sum_erase (E i) (fun j => P i j x)
    have : (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ E i, P i j x)) ^ 2 =
        ((N : ℝ) ^ 2)⁻¹ * (ψ x ^ 2 * (∑ j ∈ E i, P i j x) ^ 2) := by
      field_simp
    rw [this, h]
    congr 1
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
  have hint1 : ∫ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ E i, P i j x)) ^ 2 ∂haar N =
      ((N : ℝ) ^ 2)⁻¹ * (∑ i, ∑ j ∈ E i, ∫ x, P i j x ^ 2 * ψ x ^ 2 ∂haar N +
        ∑ i, ∑ j ∈ E i, ∑ k ∈ (E i).erase j, ∫ x, ψ x ^ 2 * (P i j x * P i k x) ∂haar N) := by
    simp_rw [hpt]
    rw [integral_const_mul, integral_add, integral_finset_sum' _ (by fun_prop), integral_finset_sum' _ (by fun_prop)]
    rotate_left
    · exact integrable_of_continuous' (by fun_prop)
    · exact integrable_of_continuous' (by fun_prop)
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_finset_sum' _ (by fun_prop)
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum' _ (by fun_prop)]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact integral_finset_sum' _ (by fun_prop)
  have hk : ∀ i, ∀ j ∈ E i, ∑ k ∈ (E i).erase j,
      ∫ x, pairFun Q i j x * P i k x * ψ x * coordPartial j ψ x ∂haar N =
      N * ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ E i, P i k x) * ψ x * coordPartial j ψ x ∂haar N -
        ∫ x, pairFun Q i j x * P i j x * ψ x * coordPartial j ψ x ∂haar N := by
    intro i j hj
    rw [← integral_finset_sum' _ (by fun_prop), ← integral_const_mul,
      ← integral_sub (integrable_of_continuous' (by fun_prop)) (integrable_of_continuous' (by fun_prop))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have h1 := Finset.sum_erase_eq_sub (f := fun k => P i k x) hj
    have e : ∑ k ∈ (E i).erase j, pairFun Q i j x * P i k x * ψ x * coordPartial j ψ x =
        pairFun Q i j x * ψ x * coordPartial j ψ x * ∑ k ∈ (E i).erase j, P i k x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, h1]
    field_simp
  have hsum2 : ∑ i, ∑ j ∈ E i, ∑ k ∈ (E i).erase j, ∫ x, ψ x ^ 2 * (P i j x * P i k x) ∂haar N =
      ∑ i, ∑ j ∈ E i, 2 * (N * ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ E i, P i k x) * ψ x *
          coordPartial j ψ x ∂haar N -
        ∫ x, pairFun Q i j x * P i j x * ψ x * coordPartial j ψ x ∂haar N) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    rw [← hk i j hj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk' => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk'
    have := ibp_triple hQ hψ hij hkj
    simp only [mul_assoc] at this ⊢
    exact this
  rw [hint1, hsum2]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp
  ring

theorem sum_abs_le_sqrt (a : Fin N → ℝ) :
    ∑ i, |a i| ≤ Real.sqrt N * Real.sqrt (∑ i, a i ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |a i|)
  simpa [sq_abs] using this

theorem pt_bilinear (L : ℝ) (hL0 : 0 ≤ L) (m : Fin N → Fin N → ℝ) (hm : ∀ i j, |m i j| ≤ L)
    (a c : Fin N → ℝ) :
    |∑ i, ∑ j ∈ Finset.univ.erase i, m i j * a i * c j| ≤
      L * N * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, c j ^ 2)) := by
  calc |∑ i, ∑ j ∈ Finset.univ.erase i, m i j * a i * c j|
      ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, m i j * a i * c j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |m i j * a i * c j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, L * (|a i| * |c j|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        calc |m i j| * |a i| * |c j| ≤ L * |a i| * |c j| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm i j) (abs_nonneg _))
                (abs_nonneg _)
          _ = L * (|a i| * |c j|) := by ring
    _ ≤ ∑ i, ∑ j, L * (|a i| * |c j|) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun j _ _ => by positivity
    _ = L * ((∑ i, |a i|) * (∑ j, |c j|)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ L * ((Real.sqrt N * Real.sqrt (∑ i, a i ^ 2)) * (Real.sqrt N * Real.sqrt (∑ j, c j ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hL0
        exact mul_le_mul (sum_abs_le_sqrt a) (sum_abs_le_sqrt c)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = L * N * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, c j ^ 2)) := by
        have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
        calc _ = L * ((Real.sqrt N * Real.sqrt N) * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, c j ^ 2))) := by ring
          _ = _ := by rw [this]; ring

theorem norm_smoothGrad_sq (ψ : Torus N → ℝ) (x : Torus N) :
    ‖smoothGrad ψ x‖ ^ 2 = ∑ j, coordPartial j ψ x ^ 2 := by
  simp [smoothGrad, EuclideanSpace.norm_sq_eq]

theorem T1_bound {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q) {ψ : Torus N → ℝ}
    (hψ : IsSmoothPeriodic ψ) {L : ℝ} (hL : ∀ t, |Q t| ≤ L) :
    |(2 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase i,
          pairFun (coordPartial 0 Q) i k x) * ψ x * coordPartial j ψ x ∂haar N| ≤
      2 * L * (Real.sqrt (∫ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
          pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N) *
        Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N)) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hq := hQ.isSmoothPeriodic_coordPartial 0
  have hcQ : ∀ i j : Fin N, Continuous (pairFun Q i j) := fun i j =>
    (isSmoothPeriodic_pairFun hQ i j).continuous_torus
  have hcq : ∀ i j : Fin N, Continuous (pairFun (coordPartial 0 Q) i j) := fun i j =>
    (isSmoothPeriodic_pairFun hq i j).continuous_torus
  have hcψ : Continuous ψ := hψ.continuous_torus
  have hcd : ∀ j, Continuous (coordPartial j ψ) := fun j => hψ.continuous_coordPartial j
  by_cases hN0 : N = 0
  · subst hN0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, abs_zero]
    positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  set a : Fin N → Torus N → ℝ := fun i x => ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
    pairFun (coordPartial 0 Q) i j x) with ha
  have hca : ∀ i, Continuous (a i) := fun i => by simp only [ha]; fun_prop
  set A : Torus N → ℝ := fun x => ∑ i, a i x ^ 2 with hA
  set C : Torus N → ℝ := fun x => ‖smoothGrad ψ x‖ ^ 2 with hC
  have hcA : Continuous A := by simp only [hA]; fun_prop
  have hcC : Continuous C := (hψ.continuous_smoothGrad.norm).pow 2
  set G : Torus N → ℝ := fun x => (2 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    pairFun Q i j x * a i x * coordPartial j ψ x with hG
  have hcG : Continuous G := by simp only [hG, ha]; fun_prop
  have hint : (2 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase i,
          pairFun (coordPartial 0 Q) i k x) * ψ x * coordPartial j ψ x ∂haar N =
      ∫ x, G x ∂haar N := by
    simp only [hG]
    rw [integral_const_mul, integral_finset_sum' _ (by simp only [ha]; fun_prop)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum' _ (by simp only [ha]; fun_prop)]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ha]; ring
  have hpt : ∀ x, |G x| ≤ 2 * L * (Real.sqrt (A x) * Real.sqrt (C x)) := by
    intro x
    have h := pt_bilinear L hL0 (fun i j => pairFun Q i j x)
      (fun i j => hL _) (fun i => a i x) (fun j => coordPartial j ψ x)
    have hCx : C x = ∑ j, coordPartial j ψ x ^ 2 := norm_smoothGrad_sq ψ x
    simp only [hG, hA, hCx, abs_mul]
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 / N)]
    calc 2 / (N : ℝ) * |∑ i, ∑ j ∈ Finset.univ.erase i, pairFun Q i j x * a i x * coordPartial j ψ x|
        ≤ 2 / (N : ℝ) * (L * N * (Real.sqrt (∑ i, a i x ^ 2) * Real.sqrt (∑ j, coordPartial j ψ x ^ 2))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by field_simp
  rw [hint]
  calc |∫ x, G x ∂haar N| ≤ ∫ x, |G x| ∂haar N := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * L * (Real.sqrt (A x) * Real.sqrt (C x)) ∂haar N :=
        integral_mono (integrable_of_continuous' hcG.abs)
          (integrable_of_continuous' (by fun_prop)) hpt
    _ = 2 * L * ∫ x, Real.sqrt (A x) * Real.sqrt (C x) ∂haar N := integral_const_mul _ _
    _ ≤ 2 * L * (Real.sqrt (∫ x, A x ∂haar N) * Real.sqrt (∫ x, C x ∂haar N)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact integral_sqrt_mul_sqrt_le A C (fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (fun x => sq_nonneg _) hcA.measurable hcC.measurable (integrable_of_continuous' hcA)
          (integrable_of_continuous' hcC)


theorem pt_T2 (L : ℝ) (hL0 : 0 ≤ L) (m p : Fin N → Fin N → ℝ) (hm : ∀ i j, |m i j| ≤ L)
    (c : Fin N → ℝ) :
    |∑ i, ∑ j ∈ Finset.univ.erase i, m i j * p i j * c j| ≤
      L * Real.sqrt N * (Real.sqrt (∑ i, ∑ j ∈ Finset.univ.erase i, p i j ^ 2) *
        Real.sqrt (∑ j, c j ^ 2)) := by
  set U : Fin N → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, p i j ^ 2 with hU
  have hU0 : ∀ i, 0 ≤ U i := fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set S : ℝ := ∑ j, c j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinner : ∀ i, |∑ j ∈ Finset.univ.erase i, m i j * p i j * c j| ≤
      L * (Real.sqrt (U i) * Real.sqrt S) := by
    intro i
    calc |∑ j ∈ Finset.univ.erase i, m i j * p i j * c j|
        ≤ ∑ j ∈ Finset.univ.erase i, |m i j * p i j * c j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, L * (|p i j| * |c j|) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          calc |m i j| * |p i j| * |c j| ≤ L * |p i j| * |c j| :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm i j) (abs_nonneg _))
                  (abs_nonneg _)
            _ = L * (|p i j| * |c j|) := by ring
      _ = L * ∑ j ∈ Finset.univ.erase i, |p i j| * |c j| := by rw [Finset.mul_sum]
      _ ≤ L * (Real.sqrt (U i) * Real.sqrt (∑ j ∈ Finset.univ.erase i, c j ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hL0
          have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ.erase i) (fun j => |p i j|)
            (fun j => |c j|)
          simpa [sq_abs, hU] using this
      _ ≤ L * (Real.sqrt (U i) * Real.sqrt S) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)) hL0
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun j _ _ => sq_nonneg _
  calc |∑ i, ∑ j ∈ Finset.univ.erase i, m i j * p i j * c j|
      ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, m i j * p i j * c j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, L * (Real.sqrt (U i) * Real.sqrt S) := Finset.sum_le_sum fun i _ => hinner i
    _ = L * Real.sqrt S * ∑ i, |Real.sqrt (U i)| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; ring
    _ ≤ L * Real.sqrt S * (Real.sqrt N * Real.sqrt (∑ i, Real.sqrt (U i) ^ 2)) :=
        mul_le_mul_of_nonneg_left (sum_abs_le_sqrt _) (by positivity)
    _ = L * Real.sqrt N * (Real.sqrt (∑ i, U i) * Real.sqrt S) := by
        have : ∑ i, Real.sqrt (U i) ^ 2 = ∑ i, U i :=
          Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hU0 i)
        rw [this]; ring

theorem T2_bound {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q) {ψ : Torus N → ℝ}
    (hψ : IsSmoothPeriodic ψ) {L : ℝ} (hL : ∀ t, |Q t| ≤ L) :
    |(2 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i j x * ψ x * coordPartial j ψ x
          ∂haar N| ≤
      2 * L * (Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N) *
        Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N)) / Real.sqrt N := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hq := hQ.isSmoothPeriodic_coordPartial 0
  have hcQ : ∀ i j : Fin N, Continuous (pairFun Q i j) := fun i j =>
    (isSmoothPeriodic_pairFun hQ i j).continuous_torus
  have hcq : ∀ i j : Fin N, Continuous (pairFun (coordPartial 0 Q) i j) := fun i j =>
    (isSmoothPeriodic_pairFun hq i j).continuous_torus
  have hcψ : Continuous ψ := hψ.continuous_torus
  have hcd : ∀ j, Continuous (coordPartial j ψ) := fun j => hψ.continuous_coordPartial j
  by_cases hN0 : N = 0
  · subst hN0
    simp
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  set A : Torus N → ℝ := fun x => ∑ i, ∑ j ∈ Finset.univ.erase i,
    (pairFun (coordPartial 0 Q) i j x * ψ x) ^ 2 with hA
  set C : Torus N → ℝ := fun x => ‖smoothGrad ψ x‖ ^ 2 with hC
  have hcA : Continuous A := by simp only [hA]; fun_prop
  have hcC : Continuous C := (hψ.continuous_smoothGrad.norm).pow 2
  set G : Torus N → ℝ := fun x => ∑ i, ∑ j ∈ Finset.univ.erase i,
    pairFun Q i j x * (pairFun (coordPartial 0 Q) i j x * ψ x) * coordPartial j ψ x with hG
  have hcG : Continuous G := by simp only [hG]; fun_prop
  have hint : ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i j x * ψ x * coordPartial j ψ x
          ∂haar N = ∫ x, G x ∂haar N := by
    simp only [hG]
    rw [integral_finset_sum' _ (by fun_prop)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum' _ (by fun_prop)]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hE : ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N = ∫ x, A x ∂haar N := by
    simp only [hA]
    rw [integral_finset_sum' _ (by fun_prop)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum' _ (by fun_prop)]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hpt : ∀ x, |G x| ≤ L * Real.sqrt N * (Real.sqrt (A x) * Real.sqrt (C x)) := by
    intro x
    have h := pt_T2 L hL0 (fun i j => pairFun Q i j x)
      (fun i j => pairFun (coordPartial 0 Q) i j x * ψ x)
      (fun i j => hL _) (fun j => coordPartial j ψ x)
    have hCx : C x = ∑ j, coordPartial j ψ x ^ 2 := norm_smoothGrad_sq ψ x
    simpa [hG, hA, hCx] using h
  have hA0 : ∀ x, 0 ≤ A x := fun x =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmain : |∫ x, G x ∂haar N| ≤
      L * Real.sqrt N * (Real.sqrt (∫ x, A x ∂haar N) * Real.sqrt (∫ x, C x ∂haar N)) := by
    calc |∫ x, G x ∂haar N| ≤ ∫ x, |G x| ∂haar N := abs_integral_le_integral_abs
      _ ≤ ∫ x, L * Real.sqrt N * (Real.sqrt (A x) * Real.sqrt (C x)) ∂haar N :=
          integral_mono (integrable_of_continuous' hcG.abs)
            (integrable_of_continuous' (by fun_prop)) hpt
      _ = L * Real.sqrt N * ∫ x, Real.sqrt (A x) * Real.sqrt (C x) ∂haar N :=
          integral_const_mul _ _
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact integral_sqrt_mul_sqrt_le A C hA0 (fun x => sq_nonneg _) hcA.measurable
            hcC.measurable (integrable_of_continuous' hcA) (integrable_of_continuous' hcC)
  rw [hint, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / (N:ℝ) ^ 2), hE]
  have hEn : 0 ≤ ∫ x, A x ∂haar N := integral_nonneg hA0
  have hsq : Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∫ x, A x ∂haar N) =
      Real.sqrt (∫ x, A x ∂haar N) / N := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq hN.le]
    field_simp
  rw [hsq]
  set s := Real.sqrt N with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hN
  have hss : s * s = N := Real.mul_self_sqrt hN.le
  have h2 : 2 / (N:ℝ) ^ 2 * (L * s * (Real.sqrt (∫ x, A x ∂haar N) * Real.sqrt (∫ x, C x ∂haar N))) =
      2 * L * (Real.sqrt (∫ x, A x ∂haar N) / N * Real.sqrt (∫ x, C x ∂haar N)) / s := by
    rw [← hss]; field_simp
  calc 2 / (N:ℝ) ^ 2 * |∫ x, G x ∂haar N|
      ≤ 2 / (N:ℝ) ^ 2 * (L * s * (Real.sqrt (∫ x, A x ∂haar N) * Real.sqrt (∫ x, C x ∂haar N))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := h2


/-- **H1023.** Distinct-label integration by parts identity.  With `Q' = coordPartial 0 Q`,
`B_i = N⁻¹ ∑_{j ≠ i} Q'(x_i - x_j)`, `b = ‖ψ B‖₂`, `L = ‖Q‖∞`, `v = ‖∇ψ‖₂` and `D` the
repeated-label quantity `N⁻² ∑_{i ≠ j} ∫ Q'(x_i - x_j)² ψ²`:
`b² - D = (2/N) ∑_{i≠j} ∫ Q_ij B_i ψ ∂_jψ - (2/N²) ∑_{i≠j} ∫ Q_ij Q'_ij ψ ∂_jψ`,
the first term is bounded by `2 L b v` and the second by `2 L √D v / √N`. -/
theorem distinct_label_integration_by_parts_identity {Q : Torus 1 → ℝ} (hQ : IsSmoothPeriodic Q)
    {ψ : Torus N → ℝ} (hψ : IsSmoothPeriodic ψ) {b D v L : ℝ}
    (hb : b = Real.sqrt (∫ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
          pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N))
    (hD : D = ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun (coordPartial 0 Q) i j x ^ 2 * ψ x ^ 2 ∂haar N)
    (hv : v = Real.sqrt (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂haar N))
    (hL : L = ⨆ t, |Q t|) :
    b ^ 2 - D =
        (2 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase i,
            pairFun (coordPartial 0 Q) i k x) * ψ x * coordPartial j ψ x ∂haar N -
        (2 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i j x * ψ x * coordPartial j ψ x
            ∂haar N ∧
      |(2 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun Q i j x * ((N : ℝ)⁻¹ * ∑ k ∈ Finset.univ.erase i,
            pairFun (coordPartial 0 Q) i k x) * ψ x * coordPartial j ψ x ∂haar N| ≤
        2 * L * b * v ∧
      |(2 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫ x, pairFun Q i j x * pairFun (coordPartial 0 Q) i j x * ψ x * coordPartial j ψ x
            ∂haar N| ≤ 2 * L * Real.sqrt D * v / Real.sqrt N := by
  have hbdd : BddAbove (Set.range fun t => |Q t|) :=
    (isCompact_range (continuous_abs.comp hQ.continuous_torus)).bddAbove
  have hLt : ∀ t, |Q t| ≤ L := fun t => hL ▸ le_ciSup hbdd t
  have hI : 0 ≤ ∫ x, ∑ i, (ψ x * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
      pairFun (coordPartial 0 Q) i j x)) ^ 2 ∂haar N :=
    integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · rw [hb, Real.sq_sqrt hI, hD]
    exact distinct_identity_core hQ hψ
  · have := T1_bound hQ hψ hLt
    rw [hb, hv]
    calc _ ≤ _ := this
      _ = _ := by ring
  · have := T2_bound hQ hψ hLt
    rw [hD, hv]
    calc _ ≤ _ := this
      _ = _ := by ring

end distinct

end DGPS.Analysis.ForceMultiplier
