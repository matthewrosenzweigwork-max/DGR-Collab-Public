import SharpSymmetricLSI.Paper.ProductFisherFormula

/-!
# (2.11): the limit `D(ρ)` (Phase 3, lane D; R6)

Slices `x ↦ W(x,y)` have weak gradient `bGrad W · y`; `W*ρ` has weak gradient `b_ρ` (Fubini);
`2∇√ρ = √ρ ∇log ρ`; hence `D(ρ) = ∫ |∇log ρ + ∇V + b_ρ|² dρ`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The affine embedding `z ↦ (z, secT y)` of `ℝ^d` into `ℝ^{2×d}`. -/
noncomputable def embY (y : Torus d) (z : Fin d → ℝ) : Fin 2 × Fin d → ℝ :=
  fun q => if q.1 = 0 then z q.2 else secT y q.2

theorem embY_lipschitz (y : Torus d) : LipschitzWith 1 (embY y) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).mpr fun q => ?_
  simp only [embY]
  split_ifs
  · exact dist_le_pi_dist z z' q.2
  · simp

theorem W2_embY (y : Torus d) (z : Fin d → ℝ) :
    (W2 W ∘ liftT) (embY y z) = W (liftT z) y := by
  have h0 : unflat (liftT (embY y z)) 0 = liftT z := by funext k; rfl
  have h1 : unflat (liftT (embY y z)) 1 = y := by
    conv_rhs => rw [← liftT_secT y]
    funext k; rfl
  simp only [Function.comp, W2]
  rw [h0, h1]

theorem embY_add_smul (y : Torus d) (z : Fin d → ℝ) (t : ℝ) (k : Fin d) :
    embY y (z + t • Pi.single k 1) = embY y z + t • Pi.single ((0 : Fin 2), k) 1 := by
  funext q
  obtain ⟨b, j⟩ := q
  simp only [embY, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hb : b = 0
  · subst hb; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, Pi.single_apply, Prod.ext_iff]
  · simp [hb, Pi.single_apply, Prod.ext_iff]

theorem secT_pairFlat (x y : Torus d) : secT (pairFlat (x, y)) = embY y (secT x) := by
  funext q
  obtain ⟨b, k⟩ := q
  simp only [embY]
  fin_cases b <;> rfl

theorem lipschitz_slice (hyp : Hyp V W KV KW) (y : Torus d) :
    LipschitzWith (Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1)
      ((fun x => W x y) ∘ liftT) := by
  have h := (lipschitz_W2 hyp (W := W)).comp (embY_lipschitz y)
  have e : (W2 W ∘ liftT) ∘ embY y = (fun x => W x y) ∘ liftT := by
    funext z; exact W2_embY y z
  rw [e] at h
  exact h

theorem lipGrad_slice (y : Torus d) (x : Torus d) (k : Fin d) :
    lipGrad (fun x => W x y) x k = bGrad W x y k := by
  simp only [lipGrad, bGrad]
  rw [show flat ![x, y] = pairFlat (x, y) from rfl, secT_pairFlat]
  unfold lineDeriv
  congr 1
  funext t
  rw [← embY_add_smul, W2_embY]
  rfl

theorem isWeakGrad_slice (hyp : Hyp V W KV KW) (y : Torus d) :
    IsWeakGrad (fun x => W x y) (fun x k => bGrad W x y k) := by
  have hc : Continuous fun x => W x y :=
    hyp.continuous_W.comp (continuous_id.prodMk continuous_const)
  have h := isWeakGrad_lipGrad hc (lipschitz_slice hyp y)
  have e : lipGrad (fun x => W x y) = fun x k => bGrad W x y k := by
    funext x k; exact lipGrad_slice y x k
  rwa [e] at h

/-- The force `b_ρ(x) = ∫ ∇₁W(x,y) ρ(y) dy` with the Lipschitz gradient. -/
noncomputable def bForceL (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (x : Torus d) (k : Fin d) :
    ℝ :=
  ∫ y, bGrad W x y k * ρ y ∂haar d

/-- **`∇(W*ρ) = b_ρ`** (Fubini on the integration by parts of the slices). -/
theorem isWeakGrad_convDens (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρm : Measurable ρ)
    (hρi : Integrable ρ (haar d)) : IsWeakGrad (convDens W ρ) (bForceL W ρ) := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  have hWm : Measurable (Function.uncurry W) := hyp.continuous_W.measurable
  set Bρ := ∫ y, |ρ y| ∂haar d
  have hWρm : Measurable (Function.uncurry fun x y => W x y * ρ y) :=
    hWm.mul (hρm.comp measurable_snd)
  have hcm : Measurable (convDens W ρ) :=
    (hWρm.stronglyMeasurable.integral_prod_right (ν := haar d)).measurable
  have hbm : ∀ k, Measurable fun x => bForceL W ρ x k := fun k =>
    (((measurable_bGrad hyp (W := W) k).mul (hρm.comp measurable_snd)).stronglyMeasurable.integral_prod_right
      (ν := haar d) (f := fun x y => bGrad W x y k * ρ y)).measurable
  have hcb : ∀ x, |convDens W ρ x| ≤ BW * Bρ := fun x => by
    unfold convDens
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |W x y * ρ y| ∂haar d ≤ ∫ y, BW * |ρ y| ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hρi.abs.const_mul BW) (Eventually.of_forall fun y => by
              show |W x y * ρ y| ≤ BW * |ρ y|
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hBW (x, y)) (abs_nonneg _))
      _ = BW * Bρ := integral_const_mul _ _
  have hbb : ∀ x k, |bForceL W ρ x k| ≤ Cb * Bρ := fun x k => by
    unfold bForceL
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |bGrad W x y k * ρ y| ∂haar d ≤ ∫ y, Cb * |ρ y| ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hρi.abs.const_mul Cb) (Eventually.of_forall fun y => by
              show |bGrad W x y k * ρ y| ≤ Cb * |ρ y|
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _))
      _ = Cb * Bρ := integral_const_mul _ _
  refine ⟨locallyIntegrable_of_bdd (hcm.comp measurable_liftT) fun x => hcb _,
    fun k => locallyIntegrable_of_bdd ((hbm k).comp measurable_liftT) fun x => hbb _ k,
    fun φ hφ hφc k => ?_⟩
  set dφ : (Fin d → ℝ) → ℝ := fun x => fderiv ℝ φ x (Pi.single k 1)
  have hdφc : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφi : Integrable dφ volume := hdφc.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) (Pi.single k 1))
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hliftm : Measurable (liftT (ι := Fin d)) := measurable_liftT
  -- Fubini, twice
  have i1 : Integrable (Function.uncurry fun (x : Fin d → ℝ) (y : Torus d) =>
      W (liftT x) y * ρ y * dφ x) (volume.prod (haar d)) := by
    refine Integrable.mono' ((hdφi.abs.mul_prod hρi.abs).const_mul BW) ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((hWm.comp (hliftm.prodMap measurable_id)).mul (hρm.comp measurable_snd)).mul
        (hdφc.measurable.comp measurable_fst) |>.aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have := hBW (liftT p.1, p.2)
      calc |W (liftT p.1) p.2| * |ρ p.2| * |dφ p.1| ≤ BW * |ρ p.2| * |dφ p.1| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (abs_nonneg _)
        _ = BW * (|dφ p.1| * |ρ p.2|) := by ring
  have i2 : Integrable (Function.uncurry fun (x : Fin d → ℝ) (y : Torus d) =>
      bGrad W (liftT x) y k * ρ y * φ x) (volume.prod (haar d)) := by
    refine Integrable.mono' ((hφi.abs.mul_prod hρi.abs).const_mul Cb) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (((measurable_bGrad hyp (W := W) k).comp (hliftm.prodMap measurable_id)).mul
        (hρm.comp measurable_snd)).mul (hφ.continuous.measurable.comp measurable_fst)
        |>.aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have := hCb (liftT p.1) p.2 k
      calc |bGrad W (liftT p.1) p.2 k| * |ρ p.2| * |φ p.1| ≤ Cb * |ρ p.2| * |φ p.1| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (abs_nonneg _)
        _ = Cb * (|φ p.1| * |ρ p.2|) := by ring
  have e1 : ∫ x, convDens W ρ (liftT x) * dφ x =
      ∫ x, ∫ y, W (liftT x) y * ρ y * dφ x ∂haar d := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [convDens]
    rw [← integral_mul_const]
  have e2 : ∫ x, bForceL W ρ (liftT x) k * φ x =
      ∫ x, ∫ y, bGrad W (liftT x) y k * ρ y * φ x ∂haar d := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [bForceL]
    rw [← integral_mul_const]
  change ∫ x, convDens W ρ (liftT x) * dφ x = -∫ x, bForceL W ρ (liftT x) k * φ x
  rw [e1, e2, integral_integral_swap i1, integral_integral_swap i2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hs := (isWeakGrad_slice hyp y).ibp φ hφ hφc k
  have l1 : ∫ x, W (liftT x) y * ρ y * dφ x = ρ y * ∫ x, W (liftT x) y * dφ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have l2 : ∫ x, bGrad W (liftT x) y k * ρ y * φ x = ρ y * ∫ x, bGrad W (liftT x) y k * φ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  show ∫ x, W (liftT x) y * ρ y * dφ x = -∫ x, bGrad W (liftT x) y k * ρ y * φ x
  rw [l1, l2]
  change ρ y * ∫ x, (fun x => W x y) (liftT x) * fderiv ℝ φ x (Pi.single k 1) = _
  rw [hs]
  ring

/-- The smooth gradient of `√ρ`. -/
noncomputable def gSqrt (ρ : Torus d → ℝ) (y : Torus d) (k : Fin d) : ℝ :=
  fderiv ℝ ((fun x => Real.sqrt (ρ x)) ∘ liftT) (secT y) (Pi.single k 1)

theorem contDiff_sqrtD {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ ∞ ((fun x => Real.sqrt (ρ x)) ∘ liftT) :=
  hs.sqrt fun x => (hpos _).ne'

/-- `2∇√ρ = √ρ ∇log ρ`. -/
theorem two_gSqrt {ρ : Torus d → ℝ} (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) (y : Torus d)
    (k : Fin d) : 2 * gSqrt ρ y k = Real.sqrt (ρ y) * gLog ρ y k := by
  set f := ρ ∘ liftT
  have hf : HasFDerivAt f (fderiv ℝ f (secT y)) (secT y) :=
    (hs.differentiable (by simp) (secT y)).hasFDerivAt
  have hfy : f (secT y) = ρ y := by simp [f, liftT_secT]
  have hne : f (secT y) ≠ 0 := by rw [hfy]; exact (hpos y).ne'
  have h1 := hf.sqrt hne
  have h2 := hf.log hne
  have e1 : gSqrt ρ y k = (1 / (2 * Real.sqrt (f (secT y)))) * fderiv ℝ f (secT y) (Pi.single k 1) := by
    unfold gSqrt
    rw [show (fun x => Real.sqrt (ρ x)) ∘ liftT = fun z => Real.sqrt (f z) from rfl, h1.fderiv]
    rfl
  have e2 : gLog ρ y k = (f (secT y))⁻¹ * fderiv ℝ f (secT y) (Pi.single k 1) := by
    unfold gLog
    rw [show logD ρ ∘ liftT = fun z => Real.log (f z) from rfl, h2.fderiv]
    rfl
  rw [e1, e2, hfy]
  have hs0 : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.mpr (hpos y)
  have hsq : Real.sqrt (ρ y) * Real.sqrt (ρ y) = ρ y := Real.mul_self_sqrt (hpos y).le
  have hinv : (ρ y)⁻¹ = (Real.sqrt (ρ y))⁻¹ * (Real.sqrt (ρ y))⁻¹ := by rw [← mul_inv, hsq]
  rw [hinv]
  field_simp

theorem bForce_eq {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar d = 1)
    (x : Torus d) (k : Fin d) : bForceL W ρ x k = ∫ y, bGrad W x y k ∂densMeasure ρ := by
  rw [bForceL, integral_densMeasure' hρ0 h1]
  congr 1; funext y; ring

/-- **`D(ρ) = ∫ ∑ₖ (aₖ + bₖ)² dρ`**, finite. -/
theorem dissipation_eq (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) :
    dissipation V W ρ = ENNReal.ofReal (∫ x, ∑ k, (aGrad V ρ x k + bForceL W ρ x k) ^ 2
      ∂densMeasure ρ) := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  haveI := isProbabilityMeasure_densMeasure' hρ0 h1
  have hρc : Continuous ρ := hs.continuous
  have hρi : Integrable ρ (haar d) := integrable_of_continuous hρc
  have hS := contDiff_sqrtD hs hpos
  have hSw : IsWeakGrad (fun x => Real.sqrt (ρ x)) (gSqrt ρ) := isWeakGrad_of_contDiff (hS.of_le (by simp))
  have hSc : Continuous fun x => Real.sqrt (ρ x) := Real.continuous_sqrt.comp hρc
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hCw := isWeakGrad_convDens hyp hρc.measurable hρi (W := W)
  have hVCw := hVw.add hCw
  obtain ⟨CS, hCS⟩ : ∃ C, ∀ y k, |gSqrt ρ y k| ≤ C := by
    obtain ⟨C, hC⟩ := exists_bound_secT (ι := Fin d)
      (h := fun x => ‖fderiv ℝ ((fun x => Real.sqrt (ρ x)) ∘ liftT) x‖)
      (hS.continuous_fderiv (by simp)).norm
    refine ⟨C, fun y k => ?_⟩
    have h1' := (fderiv ℝ ((fun x => Real.sqrt (ρ x)) ∘ liftT) (secT y)).le_opNorm (Pi.single k 1)
    have h2 : ‖(Pi.single k 1 : Fin d → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
      by_cases h : j = k
      · subst h; simp
      · simp [h]
    have h3 := hC y
    rw [abs_of_nonneg (norm_nonneg _)] at h3
    rw [gSqrt, ← Real.norm_eq_abs]
    calc _ ≤ _ := h1'
      _ ≤ ‖fderiv ℝ ((fun x => Real.sqrt (ρ x)) ∘ liftT) (secT y)‖ * 1 := by gcongr
      _ ≤ C := by rw [mul_one]; exact h3
  obtain ⟨BS, hBS⟩ := exists_bound_of_continuous hSc
  have hmem : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) := by
    refine ⟨⟨_, hSw⟩, MemLp.of_bound hSc.aestronglyMeasurable BS
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBS x), ?_⟩
    refine MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hSw⟩).aestronglyMeasurable_sqNorm)
      (Real.sqrt (Fintype.card (Fin d) * CS ^ 2)) ?_
    filter_upwards [weakGrad_ae_eq hSw] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    calc ∑ k, gSqrt ρ x k ^ 2 ≤ ∑ _k : Fin d, CS ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCS x k) 2
      _ = _ := by simp
  have hcond : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρ x) := ⟨hmem, ⟨_, hVCw⟩⟩
  unfold dissipation
  rw [if_pos hcond]
  obtain ⟨Ca, hCa⟩ := aGrad_bdd hyp hs hpos
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hbb : ∀ x k, |bForceL W ρ x k| ≤ Cb := fun x k => by
    rw [bForce_eq hρ0 h1]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |bGrad W x y k| ∂densMeasure ρ ≤ ∫ _, Cb ∂densMeasure ρ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const Cb)
            (Eventually.of_forall fun y => hCb x y k)
      _ = Cb := by simp
  have hbm : ∀ k, Measurable fun x => bForceL W ρ x k := fun k =>
    (((measurable_bGrad hyp (W := W) k).mul (hρc.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right
      (ν := haar d) (f := fun x y => bGrad W x y k * ρ y)).measurable
  set G : Torus d → ℝ := fun x => ∑ k, (aGrad V ρ x k + bForceL W ρ x k) ^ 2
  have hGm : Measurable G := Finset.measurable_sum _ fun k _ =>
    ((measurable_aGrad hyp hs hpos k).add (hbm k)).pow_const 2
  have hGb : ∀ x, |G x| ≤ Fintype.card (Fin d) * (Ca + Cb) ^ 2 := fun x => by
    rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    calc G x ≤ ∑ _k : Fin d, (Ca + Cb) ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _)
            ((abs_add_le _ _).trans (add_le_add (hCa x k) (hbb x k))) 2
      _ = _ := by simp
  have hGi : Integrable G (densMeasure ρ) := integrable_bdd' hGm.aestronglyMeasurable hGb
  rw [ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k _ => sq_nonneg _), densMeasure,
    lintegral_withDensity_eq_lintegral_mul₀ (f := fun x => ENNReal.ofReal (ρ x))
      (g := fun x => ENNReal.ofReal (G x)) (ENNReal.measurable_ofReal.comp hρc.measurable).aemeasurable
      (ENNReal.measurable_ofReal.comp hGm).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq hSw, weakGrad_ae_eq hVCw] with x hx1 hx2
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hρ0 x), hx1, hx2]
  congr 1
  simp only [G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := two_gSqrt hs hpos x k
  have hsq : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ0 x)
  rw [h2, aGrad]
  linear_combination (lipGrad V x k + gLog ρ x k + bForceL W ρ x k) ^ 2 * hsq

end SharpLSI
