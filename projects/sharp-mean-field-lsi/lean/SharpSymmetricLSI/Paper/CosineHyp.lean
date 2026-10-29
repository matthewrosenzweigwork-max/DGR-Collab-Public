import SharpSymmetricLSI.Paper.CosineTest

/-!
# R9 (3.7): the cosine model satisfies (1.2) (Phase 1)

`W_κ ∘ lift = g ∘ L` with `L(p) = p₁ - p₂` (first coordinates) and `g(s) = κ(cos 2πs - 1)`; two
integrations by parts give `∫ W_κ ∂_ξ∂_ξφ = ∫ g''(L p) (Lξ)² φ`, and
`g''(s)(Lξ)² = -aκ cos(2πs)(ξ₁ - ξ₂)² ≥ -2aκ |ξ|²`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace SharpLSI

/-- `L(p) = p₁ 0 - p₂ 0` on `ℝ^1 × ℝ^1`. -/
noncomputable def cosL : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin 1 → ℝ))

theorem cosL_apply (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) : cosL p = p.1 0 - p.2 0 := rfl

theorem cosW_lift (κ : ℝ) (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    cosW κ (liftT p.1) (liftT p.2) = κ * (Real.cos (2 * π * cosL p) - 1) := by
  rw [cosW, ← liftT_sub, gCos_coe _ (p.1 0 - p.2 0) rfl, cosL_apply]

theorem cosine_semiconvex_W (κ : ℝ)
    (φ : (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ p, 0 ≤ φ p) (ξ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    -(2 * aCos * |κ|) * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) * ∫ p, φ p ≤
      ∫ p, cosW κ (liftT p.1) (liftT p.2) * secondDirDeriv φ ξ p := by
  set c := cosL ξ with hc
  -- `G = g ∘ L` and its first two directional derivatives along `ξ`
  set g : ℝ → ℝ := fun s => κ * (Real.cos (2 * π * s) - 1) with hg
  set g1 : ℝ → ℝ := fun s => -(κ * (2 * π) * Real.sin (2 * π * s)) with hg1
  set g2 : ℝ → ℝ := fun s => -(κ * (2 * π) ^ 2 * Real.cos (2 * π * s)) with hg2
  have hd0 : ∀ s, HasDerivAt g (g1 s) s := fun s => by
    have := (((hasDerivAt_id' s).const_mul (2 * π)).cos.sub_const 1).const_mul κ
    convert this using 1; simp [hg1]; ring
  have hd1 : ∀ s, HasDerivAt g1 (g2 s) s := fun s => by
    have := (((hasDerivAt_id' s).const_mul (2 * π)).sin.const_mul (κ * (2 * π))).neg
    convert this using 1; simp [hg2]; ring
  set G := fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => g (cosL p) with hG
  set G1 := fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => g1 (cosL p) * c with hG1
  set G2 := fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => g2 (cosL p) * c * c with hG2
  have hGd : ∀ p, HasFDerivAt G (g1 (cosL p) • cosL) p := fun p =>
    (hd0 (cosL p)).comp_hasFDerivAt p cosL.hasFDerivAt
  have hG1d : ∀ p, HasFDerivAt G1 ((g2 (cosL p) * c) • cosL) p := fun p => by
    have := ((hd1 (cosL p)).comp_hasFDerivAt p cosL.hasFDerivAt).mul_const c
    exact this.congr_fderiv (by rw [smul_smul, mul_comm])
  have hfd : ∀ p, fderiv ℝ G p ξ = G1 p := fun p => by
    rw [(hGd p).fderiv]; simp [hG1, hc, smul_eq_mul]
  have hfd1 : ∀ p, fderiv ℝ G1 p ξ = G2 p := fun p => by
    rw [(hG1d p).fderiv]; simp [hG2, hc, smul_eq_mul]
  have hGc : Continuous G := by simp only [hG, hg]; fun_prop
  have hG1c : Continuous G1 := by simp only [hG1, hg1]; fun_prop
  have hG2c : Continuous G2 := by simp only [hG2, hg2]; fun_prop
  have hGdiff : Differentiable ℝ G := fun p => (hGd p).differentiableAt
  have hG1diff : Differentiable ℝ G1 := fun p => (hG1d p).differentiableAt
  -- derivatives of `φ`
  set Dφ := fun p => fderiv ℝ φ p ξ with hDφ
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hDφs : ContDiff ℝ ∞ Dφ := (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hDφd : Differentiable ℝ Dφ := hDφs.differentiable (by simp)
  have hDφc : HasCompactSupport Dφ := hφc.fderiv_apply (𝕜 := ℝ) ξ
  have hD2c : HasCompactSupport fun p => fderiv ℝ Dφ p ξ := hDφc.fderiv_apply (𝕜 := ℝ) ξ
  have hD2cont : Continuous fun p => fderiv ℝ Dφ p ξ :=
    (hDφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hW : ∀ p, cosW κ (liftT p.1) (liftT p.2) = G p := fun p => cosW_lift κ p
  simp_rw [hW]
  -- two integrations by parts
  have : (volume : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have i1 : Integrable (fun p => fderiv ℝ G p ξ * Dφ p) volume := by
    simp_rw [hfd]
    exact (hG1c.mul hDφs.continuous).integrable_of_hasCompactSupport hDφc.mul_left
  have i2 : Integrable (fun p => G p * fderiv ℝ Dφ p ξ) volume :=
    (hGc.mul hD2cont).integrable_of_hasCompactSupport hD2c.mul_left
  have i3 : Integrable (fun p => G p * Dφ p) volume :=
    (hGc.mul hDφs.continuous).integrable_of_hasCompactSupport hDφc.mul_left
  have ibp1 : ∫ p, G p * fderiv ℝ Dφ p ξ = -∫ p, G1 p * Dφ p := by
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun p _ => hGdiff p) (fun p _ => hDφd p)
    simpa [hfd] using this
  have j1 : Integrable (fun p => fderiv ℝ G1 p ξ * φ p) volume := by
    simp_rw [hfd1]
    exact (hG2c.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have j2 : Integrable (fun p => G1 p * fderiv ℝ φ p ξ) volume :=
    (hG1c.mul hDφs.continuous).integrable_of_hasCompactSupport hDφc.mul_left
  have j3 : Integrable (fun p => G1 p * φ p) volume :=
    (hG1c.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have ibp2 : ∫ p, G1 p * Dφ p = -∫ p, G2 p * φ p := by
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable j1 j2 j3
      (fun p _ => hG1diff p) (fun p _ => hφd p)
    simpa [hfd1] using this
  have hsec : ∀ p, secondDirDeriv φ ξ p = fderiv ℝ Dφ p ξ := fun p => rfl
  simp_rw [hsec, ibp1, ibp2, neg_neg]
  -- pointwise lower bound
  have hc2 : c ^ 2 ≤ 2 * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) := by
    simp only [hc, cosL_apply, Fin.sum_univ_one]
    nlinarith [sq_nonneg (ξ.1 0 + ξ.2 0)]
  have hpt : ∀ p, -(2 * aCos * |κ|) * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) * φ p ≤ G2 p * φ p := by
    intro p
    apply mul_le_mul_of_nonneg_right _ (hφ0 p)
    simp only [hG2, hg2, aCos]
    have h0 : |κ * Real.cos (2 * π * cosL p)| ≤ |κ| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have h1 : κ * Real.cos (2 * π * cosL p) ≤ |κ| := (le_abs_self _).trans h0
    have hP : 0 ≤ (2 * π) ^ 2 := by positivity
    have e1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hP (sq_nonneg c))
    have e2 := mul_le_mul_of_nonneg_left hc2 (mul_nonneg (abs_nonneg κ) hP)
    nlinarith [e1, e2]
  rw [← integral_const_mul]
  exact integral_mono (((continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport
      hφc.mul_left) ((hG2c.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left) hpt

theorem cosine_hyp_aux {κ : ℝ} (hκ : 0 < κ) : Hyp cosV (cosW κ) 0 (2 * aCos * κ) := by
  have ha : 0 < aCos := by unfold aCos; positivity
  have hsymm : ∀ x y : Torus 1, cosW κ x y = cosW κ y x := by
    intro x y
    simp only [cosW, gCos]
    congr 2
    simp only [expT, fourier_apply, one_smul, Pi.sub_apply]
    rw [show y 0 - x 0 = -(x 0 - y 0) by abel, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj,
      Complex.conj_re]
  refine ⟨le_rfl, by positivity, continuous_const, ?_, ?_, ?_, hsymm, ?_⟩
  · simp only [Function.uncurry_def, cosW]
    exact continuous_const.mul ((continuous_gCos.comp (continuous_fst.sub continuous_snd)).sub
      continuous_const)
  · intro φ _ _ _ ξ
    simp [cosV]
  · intro φ hφ hφc hφ0 ξ
    have := cosine_semiconvex_W κ φ hφ hφc hφ0 ξ
    rwa [abs_of_pos hκ] at this
  · intro x
    simp [cosW, gCos, expT]

/-- (1.2) for the cosine model for every `κ`, with `K_W = 2a|κ|`. -/
theorem cosine_hyp_all (κ : ℝ) : Hyp cosV (cosW κ) 0 (2 * aCos * |κ|) := by
  have ha : 0 < aCos := by unfold aCos; positivity
  rcases eq_or_ne κ 0 with h0 | h0
  · refine ⟨le_rfl, by positivity, continuous_const, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.uncurry_def, cosW, h0, zero_mul]; exact continuous_const
    · intro φ _ _ _ ξ; simp [cosV]
    · intro φ _ _ _ ξ; simp [cosW, h0]
    · intro x y; simp [cosW, h0]
    · intro x; simp [cosW, h0]
  · have hs := cosine_hyp_aux (κ := |κ|) (abs_pos.mpr h0)
    refine ⟨le_rfl, by positivity, continuous_const, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Function.uncurry_def, cosW]
      exact continuous_const.mul ((continuous_gCos.comp (continuous_fst.sub continuous_snd)).sub
        continuous_const)
    · intro φ _ _ _ ξ; simp [cosV]
    · exact fun φ hφ hφc hφ0 ξ => cosine_semiconvex_W κ φ hφ hφc hφ0 ξ
    · intro x y
      have := hs.symm x y
      simp only [cosW] at this ⊢
      rcases (mul_right_inj' (abs_pos.mpr h0).ne').mp this with h
      rw [h]
    · intro x
      have := hs.diag x
      simp only [cosW] at this ⊢
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (abs_pos.mpr h0).ne'
      · rw [h, mul_zero]

end SharpLSI
