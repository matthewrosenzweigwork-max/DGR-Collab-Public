import DGPS.FiniteN.AnisotropicQuarticLocalChart

/-!
# Actual quartic local Dirichlet restoration

The final declaration has no Jacobian, metric, or square-root-gap premise. Its single actual
FIN068 witness supplies the flat potential and curvature, density Jacobian, and coordinate
metric. Smooth compactly supported auxiliary tests are transported
through the actual inverse chart with genuine integrability of both weighted forms.
-/

open MeasureTheory Filter Topology Set
open DGPS.Models DGPS.Frontier.FIN068 DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.FiniteN

private theorem triangular_metric_point
    (D L K : ℝ × ℝ →L[ℝ] ℝ)
    (hD : D = L.comp (K.prod (ContinuousLinearMap.snd ℝ ℝ ℝ)))
    (hm : ∀ ξ : Fin 2 → ℝ,
      sqnorm_FIN06836 ξ / (1 + 8 / quarticA_FIN06803) ≤
        sqnorm_FIN06836 ((Matrix.transpose
          (Matrix.of ![![K (1, 0), K (0, 1)], ![0, 1]])).mulVec ξ)) :
    (L (0, 1)) ^ 2 / (1 + 8 / quarticA_FIN06803) ≤
      (D (1, 0)) ^ 2 + (D (0, 1)) ^ 2 := by
  have h0 : D (1, 0) = K (1, 0) * L (1, 0) := by
    rw [hD]
    change L (K (1, 0), 0) = _
    rw [lin_FIN06835]
    simp
  have h1 : D (0, 1) = K (0, 1) * L (1, 0) + L (0, 1) := by
    rw [hD]
    change L (K (0, 1), 1) = _
    rw [lin_FIN06835]
    simp
  have h := hm ![L (1, 0), L (0, 1)]
  simp [sqnorm_FIN06836, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  rw [h0, h1]
  have hA : 0 < quarticA_FIN06803 := fin068_03_constants_exact_cancellation.2.2.1
  have hden : 0 < 1 + 8 / quarticA_FIN06803 := by positivity
  exact (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (L (1, 0))]) hden.le).trans h

private theorem source_fderiv_of_chart
    (W : Set (ℝ × ℝ)) (hWo : IsOpen W) (v F G : ℝ × ℝ → ℝ)
    (hv : ContDiffOn ℝ ∞ v W) (hG : ContDiff ℝ ∞ G)
    (heq : ∀ p ∈ W, F p = G (v p, p.2)) (p : ℝ × ℝ) (hp : p ∈ W) :
    fderiv ℝ F p = (fderiv ℝ G (v p, p.2)).comp
      ((fderiv ℝ v p).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  have hloc : F =ᶠ[nhds p] fun z => G (v z, z.2) := by
    filter_upwards [hWo.mem_nhds hp] with z hz
    exact heq z hz
  have hvp := ((hv.contDiffAt (hWo.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hsnd : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hd := ((hG.differentiable (by simp)) (v p, p.2)).hasFDerivAt.comp p (hvp.prodMk hsnd)
  rw [hloc.fderiv_eq]
  change fderiv ℝ (G ∘ fun z : ℝ × ℝ => (v z, z.2)) p = _
  exact hd.fderiv

private theorem chart_weighted_lower
    (Ψ : ℝ × ℝ → ℝ) (hΨ : Continuous Ψ) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (c ε δ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hδ : 0 < δ)
    (v X : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ)) (hWo : IsOpen W)
    (hv : ContDiffOn ℝ ∞ v W)
    (hX : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (X q, q.2)) (Ioo (-ε) ε ×ˢ Ioo (-δ) δ))
    (hTU : ∀ p ∈ W, (v p, p.2) ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ)
    (hRQ : ∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, (X q, q.2) ∈ W)
    (hTR : ∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, v (X q, q.2) = q.1)
    (hRT : ∀ p ∈ W, X (v p, p.2) = p.1)
    (hpot : ∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, Ψ (X q, q.2) = q.1 ^ 2 / 2 + Φ q.2)
    (hcurv : ∀ y : ℝ, |y| < δ → deriv (deriv Φ) y ≤ -c * y ^ 2)
    (hjac : ∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ,
      1 / (2 * Real.sqrt quarticA_FIN06803) ≤
        (fderiv ℝ (fun z : ℝ × ℝ => (X z, z.2)) q).det ∧
      (fderiv ℝ (fun z : ℝ × ℝ => (X z, z.2)) q).det ≤ 2 / Real.sqrt quarticA_FIN06803)
    (hmetric : ∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, ∀ ξ : Fin 2 → ℝ,
      sqnorm_FIN06836 ξ / (1 + 8 / quarticA_FIN06803) ≤
        sqnorm_FIN06836 ((Matrix.transpose
          (Matrix.of ![![fderiv ℝ v (X q, q.2) (1, 0),
            fderiv ℝ v (X q, q.2) (0, 1)], ![0, 1]])).mulVec ξ))
    (N : ℝ) (hN : 0 ≤ N) (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hFU : tsupport F ⊆ W) :
    ((1 / (2 * Real.sqrt quarticA_FIN06803) / (1 + 8 / quarticA_FIN06803)) /
      (2 / Real.sqrt quarticA_FIN06803)) * Real.sqrt (c * N / 2) *
        (∫ p, F p ^ 2 * Real.exp (-(N * Ψ p))) ≤
      ∫ p, ((fderiv ℝ F p (1, 0)) ^ 2 + (fderiv ℝ F p (0, 1)) ^ 2) *
        Real.exp (-(N * Ψ p)) := by
  classical
  let Q : Set (ℝ × ℝ) := Ioo (-ε) ε ×ˢ Ioo (-δ) δ
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (v p, p.2)
  let R : ℝ × ℝ → ℝ × ℝ := fun q => (X q, q.2)
  let G : ℝ × ℝ → ℝ := Q.indicator (fun q => F (R q))
  let w : ℝ × ℝ → ℝ := fun q => Real.exp (-(N * (q.1 ^ 2 / 2 + Φ q.2)))
  let j : ℝ × ℝ → ℝ := fun q => (fderiv ℝ R q).det
  let jmin : ℝ := 1 / (2 * Real.sqrt quarticA_FIN06803)
  let jmax : ℝ := 2 / Real.sqrt quarticA_FIN06803
  let D : ℝ := 1 + 8 / quarticA_FIN06803
  let K : ℝ := jmin / D
  have hA : 0 < quarticA_FIN06803 := fin068_03_constants_exact_cancellation.2.2.1
  have hjmin : 0 < jmin := by dsimp [jmin]; positivity
  have hjmax : 0 < jmax := by dsimp [jmax]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := div_pos hjmin hD
  have hQo : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hT : ContDiffOn ℝ ∞ T W := hv.prodMk contDiffOn_snd
  have hTR' : ∀ q ∈ Q, T (R q) = q := by
    intro q hq
    exact Prod.ext (hTR q hq) rfl
  have hRT' : ∀ p ∈ W, R (T p) = p := by
    intro p hp
    exact Prod.ext (hRT p hp) rfl
  obtain ⟨hGs, hGc, hGder⟩ := quartic_chart_pullback W Q hQo T R hT.continuousOn hX
    hTU hTR' F hF hFc hFU
  have hGq : ∀ q ∈ Q, G q = F (R q) := fun q hq => Set.indicator_of_mem hq _
  have hFG : ∀ p ∈ W, F p = G (T p) := by
    intro p hp
    rw [hGq (T p) (hTU p hp), hRT' p hp]
  have hGQ : tsupport G ⊆ Q := by
    let C := T '' tsupport F
    have hCc : IsCompact C := hFc.isCompact.image_of_continuousOn (hT.continuousOn.mono hFU)
    have hCQ : C ⊆ Q := by
      rintro q ⟨p, hp, rfl⟩
      exact hTU p (hFU hp)
    refine (closure_minimal ?_ hCc.isClosed).trans hCQ
    intro q hq
    change G q ≠ 0 at hq
    by_cases hqQ : q ∈ Q
    · exact ⟨R q, subset_tsupport F (show R q ∈ Function.support F from by
        change F (R q) ≠ 0
        simpa only [hGq q hqQ] using hq), hTR' q hqQ⟩
    · exact False.elim (hq (Set.indicator_of_notMem hqQ _))
  have hGout : ∀ q, q ∉ Q → G q = 0 := fun q hq => Set.indicator_of_notMem hq _
  have hDGout : ∀ q, q ∉ Q → fderiv ℝ G q = 0 :=
    fun q hq => fderiv_of_notMem_tsupport ℝ (fun h => hq (hGQ h))
  have hDF : ∀ q ∈ Q, fderiv ℝ F (R q) =
      (fderiv ℝ G q).comp ((fderiv ℝ v (R q)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    intro q hq
    have h := source_fderiv_of_chart W hWo v F G hv hGs hFG (R q) (hRQ q hq)
    change fderiv ℝ F (R q) = (fderiv ℝ G (T (R q))).comp _ at h
    rw [hTR' q hq] at h
    exact h
  have hpoint : ∀ q ∈ Q,
      (fderiv ℝ G q (0, 1)) ^ 2 / D ≤
        (fderiv ℝ F (R q) (1, 0)) ^ 2 + (fderiv ℝ F (R q) (0, 1)) ^ 2 := by
    intro q hq
    exact triangular_metric_point (fderiv ℝ F (R q)) (fderiv ℝ G q)
      (fderiv ℝ v (R q)) (hDF q hq) (hmetric q hq)
  have hjabs : ∀ q ∈ Q, |j q| = j q := by
    intro q hq
    exact abs_of_pos (hjmin.trans_le (hjac q hq).1)
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hGmi : Integrable (fun q => G q ^ 2 * w q) :=
    ((hGs.continuous.pow 2).mul hwc).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hGc.isCompact fun q hq => by
        change G q ^ 2 * w q = 0
        change q ∉ tsupport G at hq
        have hz : G q = 0 := image_eq_zero_of_notMem_tsupport hq
        rw [hz]; simp)
  have hDGc : HasCompactSupport (fun q => fderiv ℝ G q (0, 1)) := hGc.fderiv_apply ℝ (0, 1)
  have hDGcont : Continuous (fun q => fderiv ℝ G q (0, 1)) :=
    (hGs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGdi : Integrable (fun q => (fderiv ℝ G q (0, 1)) ^ 2 * w q) :=
    ((hDGcont.pow 2).mul hwc).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hDGc.isCompact fun q hq => by
        change (fderiv ℝ G q (0, 1)) ^ 2 * w q = 0
        rw [image_eq_zero_of_notMem_tsupport hq]; simp)
  let M : ℝ × ℝ → ℝ := fun p => F p ^ 2 * Real.exp (-(N * Ψ p))
  let E : ℝ × ℝ → ℝ := fun p =>
    ((fderiv ℝ F p (1, 0)) ^ 2 + (fderiv ℝ F p (0, 1)) ^ 2) * Real.exp (-(N * Ψ p))
  have hMc : Continuous M := by dsimp [M]; exact (hF.continuous.pow 2).mul (Real.continuous_exp.comp (hΨ.const_mul N).neg)
  have hEc : Continuous E := by
    dsimp [E]
    exact ((((hF.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).add
      (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)).mul
      (Real.continuous_exp.comp (hΨ.const_mul N).neg)
  have hMzero : ∀ p, p ∉ tsupport F → M p = 0 := by
    intro p hp
    simp [M, image_eq_zero_of_notMem_tsupport hp]
  have hEzero : ∀ p, p ∉ tsupport F → E p = 0 := by
    intro p hp
    simp [E, fderiv_of_notMem_tsupport ℝ hp]
  have hMs : tsupport M ⊆ W := by
    refine (closure_minimal (fun p hp => ?_) (isClosed_tsupport F)).trans hFU
    by_contra hn
    exact hp (hMzero p hn)
  have hEs : tsupport E ⊆ W := by
    refine (closure_minimal (fun p hp => ?_) (isClosed_tsupport F)).trans hFU
    by_contra hn
    exact hp (hEzero p hn)
  obtain ⟨hMi, hMeq⟩ := quartic_chart_change_of_variables W Q hQo T R hX
    hTU hRQ hTR' hRT' M hMc (HasCompactSupport.intro hFc.isCompact hMzero) hMs
  obtain ⟨hEi, hEeq⟩ := quartic_chart_change_of_variables W Q hQo T R hX
    hTU hRQ hTR' hRT' E hEc (HasCompactSupport.intro hFc.isCompact hEzero) hEs
  have hmass : (∫ p, M p) ≤ jmax * ∫ q, G q ^ 2 * w q := by
    rw [hMeq]
    calc
      _ ≤ ∫ q in Q, jmax * (G q ^ 2 * w q) := by
        refine integral_mono_ae hMi ((hGmi.const_mul jmax).integrableOn) ?_
        filter_upwards [ae_restrict_mem hQo.measurableSet] with q hq
        change |j q| * (F (R q) ^ 2 * Real.exp (-(N * Ψ (R q)))) ≤ _
        rw [hjabs q hq, hpot q hq, ← hGq q hq]
        exact mul_le_mul_of_nonneg_right (hjac q hq).2
          (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ = _ := by
        rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro q hq
        rw [hGout q hq]
        simp
  have henergy : K * (∫ q, (fderiv ℝ G q (0, 1)) ^ 2 * w q) ≤ ∫ p, E p := by
    rw [hEeq]
    calc
      _ = ∫ q in Q, K * ((fderiv ℝ G q (0, 1)) ^ 2 * w q) := by
        rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro q hq
        rw [hDGout q hq]
        simp
      _ ≤ _ := by
        refine integral_mono_ae ((hGdi.const_mul K).integrableOn) hEi ?_
        filter_upwards [ae_restrict_mem hQo.measurableSet] with q hq
        change K * ((fderiv ℝ G q (0, 1)) ^ 2 * w q) ≤
          |j q| * (((fderiv ℝ F (R q) (1, 0)) ^ 2 +
            (fderiv ℝ F (R q) (0, 1)) ^ 2) * Real.exp (-(N * Ψ (R q))))
        rw [hjabs q hq, hpot q hq]
        have hp := mul_le_mul_of_nonneg_left (hpoint q hq) hjmin.le
        have hj := mul_le_mul_of_nonneg_right (hjac q hq).1
          (add_nonneg (sq_nonneg (fderiv ℝ F (R q) (1, 0)))
            (sq_nonneg (fderiv ℝ F (R q) (0, 1))))
        have hh := mul_le_mul_of_nonneg_right (hp.trans hj) (Real.exp_pos (-(N *
          (q.1 ^ 2 / 2 + Φ q.2)))).le
        dsimp [K, w, j, R] at hh ⊢
        convert hh using 1 <;> ring
  have hgap := quartic_flat_local_dirichlet Φ hΦ {y | |y| < δ} c hc.le hcurv N hN G hGs hGc
    (fun q hq => abs_lt.mpr (hGQ hq).2)
  change Real.sqrt (c * N / 2) * (∫ q, G q ^ 2 * w q) ≤
    ∫ q, (fderiv ℝ G q (0, 1)) ^ 2 * w q at hgap
  change (K / jmax) * Real.sqrt (c * N / 2) * (∫ p, M p) ≤ ∫ p, E p
  calc
    _ ≤ (K / jmax) * Real.sqrt (c * N / 2) *
        (jmax * ∫ q, G q ^ 2 * w q) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = K * (Real.sqrt (c * N / 2) * ∫ q, G q ^ 2 * w q) := by
      field_simp [ne_of_gt hjmax] <;> ring
    _ ≤ K * ∫ q, (fderiv ℝ G q (0, 1)) ^ 2 * w q :=
      mul_le_mul_of_nonneg_left hgap hK.le
    _ ≤ _ := henergy

/-- The actual quartic model has a fixed open remote patch with the square-root local
Dirichlet lower bound. This is the product-coordinate statement with the exact sum of
squared coordinate derivatives; the Euclidean normalization is supplied separately. -/
theorem quartic_product_local_dirichlet :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (-4, 0) ∈ W ∧ ∃ a : ℝ, 0 < a ∧
      ∀ N : ℝ, 1 ≤ N → ∀ F : ℝ × ℝ → ℝ,
        ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ W →
        a * Real.sqrt N *
            (∫ p : ℝ × ℝ, F p ^ 2 * Real.exp (-(N * quarticPsi_FIN066 !₂[p.1, p.2]))) ≤
          ∫ p : ℝ × ℝ, ((fderiv ℝ F p (1, 0)) ^ 2 + (fderiv ℝ F p (0, 1)) ^ 2) *
            Real.exp (-(N * quarticPsi_FIN066 !₂[p.1, p.2])) := by
  obtain ⟨Φ, hΦ, c, ε, δ, hc, hε, hδ, v, X, W, hWo, hW0, hv, hX,
    hTU, hRQ, hTR, hRT, hpot, hcurv, hjac, hmetric⟩ := quartic_smooth_flat_chart
  have hA : 0 < quarticA_FIN06803 := fin068_03_constants_exact_cancellation.2.2.1
  have hmap : ContDiff ℝ ∞ amap_FIN066 := by
    rw [show amap_FIN066 = fun z => Alin_FIN066 z +
      !₂[-1 / Real.sqrt quarticKappa, 0] from funext amap_eq_FIN066]
    exact Alin_FIN066.contDiff.add contDiff_const
  have hψ : Continuous quarticPsi_FIN066 := by
    rw [quarticPsi_eq_FIN066]
    exact (DGPS.FiniteN.AttractiveLandscape.contDiff_psi_infty
      continuous_U_FIN066 continuous_Phi_FIN066).continuous.comp hmap.continuous
  have hΨ : Continuous (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[p.1, p.2]) :=
    hψ.comp (by fun_prop)
  let a : ℝ := ((1 / (2 * Real.sqrt quarticA_FIN06803) / (1 + 8 / quarticA_FIN06803)) /
    (2 / Real.sqrt quarticA_FIN06803)) * Real.sqrt (c / 2)
  refine ⟨W, hWo, hW0, a, by dsimp [a]; positivity, fun N hN F hF hFc hFU => ?_⟩
  have h := chart_weighted_lower (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[p.1, p.2])
    hΨ Φ hΦ c ε δ hc hε hδ v X W hWo hv hX hTU hRQ hTR hRT hpot hcurv hjac hmetric
    N (by linarith) F hF hFc hFU
  have hfactor : Real.sqrt (c * N / 2) = Real.sqrt (c / 2) * Real.sqrt N := by
    rw [show c * N / 2 = (c / 2) * N by ring, Real.sqrt_mul (by positivity : 0 ≤ c / 2)]
  rw [hfactor] at h
  simpa only [a, mul_assoc] using h

end DGPS.FiniteN
