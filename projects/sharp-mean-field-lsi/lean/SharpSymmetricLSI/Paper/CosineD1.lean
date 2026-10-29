import SharpSymmetricLSI.Paper.CosineHyp

/-!
# The `d`-dimensional cosine model (1): definition and (1.2)

`W_κ(x,y) = κ ∑ₖ (cos 2π(xₖ - yₖ) - 1)` on `𝕋^d` (`cosWd`), the sum over `k` of the circle
kernel `cosW κ` applied to the `k`-th coordinates (`cosWd_eq_sum`). It satisfies (1.2) with
`K_V = 0`, `K_W = 2aκ` (`hyp_cosWd`): each summand has Hessian `≥ -aκ (ξ₁ₖ - ξ₂ₖ)²`
(`cosD_semiconvex_lin`), and `(ξ₁ₖ - ξ₂ₖ)² ≤ 2(ξ₁ₖ² + ξ₂ₖ²)`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace SharpLSI

variable {d : ℕ}

/-- The `d`-dimensional cosine interaction `κ ∑ₖ (cos 2π(xₖ - yₖ) - 1)`. -/
noncomputable def cosWd (κ : ℝ) (x y : Torus d) : ℝ :=
  κ * ∑ k, ((fourier 1 (x k - y k)).re - 1)

/-- The `k`-th coordinate of a point of `𝕋^d`, as a point of `𝕋^1`. -/
def cosDproj (k : Fin d) (x : Torus d) : Torus 1 := fun _ => x k

theorem cosW_cosDproj (κ : ℝ) (k : Fin d) (x y : Torus d) :
    cosW κ (cosDproj k x) (cosDproj k y) = κ * ((fourier 1 (x k - y k)).re - 1) := rfl

theorem cosWd_eq_sum (κ : ℝ) (x y : Torus d) :
    cosWd κ x y = ∑ k, cosW κ (cosDproj k x) (cosDproj k y) := by
  rw [cosWd, Finset.mul_sum]; rfl

/-- For `d = 1`, `cosWd` is the circle kernel `cosW`. -/
theorem cosWd_one (κ : ℝ) : cosWd (d := 1) κ = cosW κ := by
  funext x y
  rw [cosWd_eq_sum, Fin.sum_univ_one]
  have hx : cosDproj 0 x = x := funext fun i => by rw [Subsingleton.elim i 0]; rfl
  have hy : cosDproj 0 y = y := funext fun i => by rw [Subsingleton.elim i 0]; rfl
  rw [hx, hy]

theorem continuous_cosDproj (k : Fin d) : Continuous (cosDproj k) :=
  continuous_pi fun _ => continuous_apply k

theorem cosWd_lift (κ : ℝ) (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    cosWd κ (liftT p.1) (liftT p.2) = ∑ k, κ * (Real.cos (2 * π * (p.1 k - p.2 k)) - 1) := by
  rw [cosWd_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cosW, gCos_coe _ (p.1 k - p.2 k)]
  simp [cosDproj, liftT]

/-- A cosine of a linear form is `(-aκ (Lξ)²)`-semiconvex along `ξ`, distributionally. -/
theorem cosD_semiconvex_lin {κ : ℝ} (hκ : 0 ≤ κ)
    (L : ((Fin d → ℝ) × (Fin d → ℝ)) →L[ℝ] ℝ)
    (φ : (Fin d → ℝ) × (Fin d → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ p, 0 ≤ φ p) (ξ : (Fin d → ℝ) × (Fin d → ℝ)) :
    -(aCos * κ * (L ξ) ^ 2) * ∫ p, φ p ≤
      ∫ p, κ * (Real.cos (2 * π * L p) - 1) * secondDirDeriv φ ξ p := by
  set c := L ξ with hc
  set g : ℝ → ℝ := fun s => κ * (Real.cos (2 * π * s) - 1) with hg
  set g1 : ℝ → ℝ := fun s => -(κ * (2 * π) * Real.sin (2 * π * s)) with hg1
  set g2 : ℝ → ℝ := fun s => -(κ * (2 * π) ^ 2 * Real.cos (2 * π * s)) with hg2
  have hd0 : ∀ s, HasDerivAt g (g1 s) s := fun s => by
    have := (((hasDerivAt_id' s).const_mul (2 * π)).cos.sub_const 1).const_mul κ
    convert this using 1; simp [hg1]; ring
  have hd1 : ∀ s, HasDerivAt g1 (g2 s) s := fun s => by
    have := (((hasDerivAt_id' s).const_mul (2 * π)).sin.const_mul (κ * (2 * π))).neg
    convert this using 1; simp [hg2]; ring
  set G := fun p : (Fin d → ℝ) × (Fin d → ℝ) => g (L p) with hG
  set G1 := fun p : (Fin d → ℝ) × (Fin d → ℝ) => g1 (L p) * c with hG1
  set G2 := fun p : (Fin d → ℝ) × (Fin d → ℝ) => g2 (L p) * c * c with hG2
  have hGd : ∀ p, HasFDerivAt G (g1 (L p) • L) p := fun p =>
    (hd0 (L p)).comp_hasFDerivAt p L.hasFDerivAt
  have hG1d : ∀ p, HasFDerivAt G1 ((g2 (L p) * c) • L) p := fun p => by
    have := ((hd1 (L p)).comp_hasFDerivAt p L.hasFDerivAt).mul_const c
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
  set Dφ := fun p => fderiv ℝ φ p ξ with hDφ
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hDφs : ContDiff ℝ ∞ Dφ := (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hDφd : Differentiable ℝ Dφ := hDφs.differentiable (by simp)
  have hDφc : HasCompactSupport Dφ := hφc.fderiv_apply (𝕜 := ℝ) ξ
  have hD2c : HasCompactSupport fun p => fderiv ℝ Dφ p ξ := hDφc.fderiv_apply (𝕜 := ℝ) ξ
  have hD2cont : Continuous fun p => fderiv ℝ Dφ p ξ :=
    (hDφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hW : ∀ p, κ * (Real.cos (2 * π * L p) - 1) = G p := fun p => rfl
  simp_rw [hW]
  have : (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).IsAddHaarMeasure :=
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
  have hpt : ∀ p, -(aCos * κ * c ^ 2) * φ p ≤ G2 p * φ p := by
    intro p
    apply mul_le_mul_of_nonneg_right _ (hφ0 p)
    simp only [hG2, hg2, aCos]
    have h1 : κ * Real.cos (2 * π * L p) ≤ κ :=
      mul_le_of_le_one_right hκ (Real.cos_le_one _)
    have hP : 0 ≤ (2 * π) ^ 2 * c ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hP]
  rw [← integral_const_mul]
  exact integral_mono (((continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport
      hφc.mul_left) ((hG2c.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left) hpt

/-- `p ↦ p₁ₖ - p₂ₖ`. -/
noncomputable def cosDL (k : Fin d) : ((Fin d → ℝ) × (Fin d → ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).comp
      (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin d → ℝ)) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).comp
      (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))

theorem cosDL_apply (k : Fin d) (p : (Fin d → ℝ) × (Fin d → ℝ)) : cosDL k p = p.1 k - p.2 k := rfl

theorem continuous_cosWd (κ : ℝ) : Continuous (Function.uncurry (cosWd (d := d) κ)) := by
  simp only [Function.uncurry_def, cosWd]
  exact continuous_const.mul (continuous_finsetSum _ fun k _ =>
    (Complex.continuous_re.comp ((fourier 1).continuous.comp
      (((continuous_apply k).comp continuous_fst).sub ((continuous_apply k).comp
        continuous_snd)))).sub continuous_const)

/-- **(1.2) for the `d`-dimensional cosine model**, `K_V = 0`, `K_W = 2aκ`. -/
theorem hyp_cosWd {κ : ℝ} (hκ : 0 < κ) :
    Hyp (d := d) (fun _ => 0) (cosWd κ) 0 (2 * aCos * κ) := by
  have ha : 0 < aCos := by unfold aCos; positivity
  refine ⟨le_rfl, by positivity, continuous_const, continuous_cosWd κ, ?_, ?_, ?_, ?_⟩
  · intro φ _ _ _ ξ; simp
  · intro φ hφ hφc hφ0 ξ
    have hDφs : ContDiff ℝ ∞ fun p => fderiv ℝ φ p ξ :=
      (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hS : Continuous (secondDirDeriv φ ξ) :=
      (hDφs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hSc : HasCompactSupport (secondDirDeriv φ ξ) :=
      (hφc.fderiv_apply (𝕜 := ℝ) ξ).fderiv_apply (𝕜 := ℝ) ξ
    simp_rw [cosWd_lift, Finset.sum_mul]
    rw [integral_finsetSum _ fun k _ => ?_]
    swap
    · exact ((continuous_const.mul ((Real.continuous_cos.comp (continuous_const.mul
        (((continuous_apply k).comp continuous_fst).sub ((continuous_apply k).comp
          continuous_snd)))).sub continuous_const)).mul hS).integrable_of_hasCompactSupport
        hSc.mul_left
    have hk := fun k => cosD_semiconvex_lin hκ.le (cosDL k) φ hφ hφc hφ0 ξ
    simp only [cosDL_apply] at hk
    have hφi : 0 ≤ ∫ p, φ p := integral_nonneg hφ0
    calc -(2 * aCos * κ) * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) * ∫ p, φ p
        ≤ ∑ k, -(aCos * κ * (ξ.1 k - ξ.2 k) ^ 2) * ∫ p, φ p := by
          have e : -(2 * aCos * κ) * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) * ∫ p, φ p =
              ∑ k, -(2 * aCos * κ) * (ξ.1 k ^ 2 + ξ.2 k ^ 2) * ∫ p, φ p := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          rw [e]
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ hφi
          have : (ξ.1 k - ξ.2 k) ^ 2 ≤ 2 * (ξ.1 k ^ 2 + ξ.2 k ^ 2) := by
            nlinarith [sq_nonneg (ξ.1 k + ξ.2 k)]
          nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ aCos * κ)]
      _ ≤ _ := Finset.sum_le_sum fun k _ => hk k
  · intro x y
    simp only [cosWd]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [fourier_apply, one_smul]
    rw [show y k - x k = -(x k - y k) by abel, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj,
      Complex.conj_re]
  · intro x
    simp [cosWd]

end SharpLSI
