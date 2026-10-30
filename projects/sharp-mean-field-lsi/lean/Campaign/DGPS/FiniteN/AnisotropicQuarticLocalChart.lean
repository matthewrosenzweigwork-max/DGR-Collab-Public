import DGPS.FiniteN.AnisotropicQuarticJacobian
import DGPS.FiniteN.AnisotropicQuarticEuclidean
import DGPS.FiniteN.AnisotropicQuarticReducedExtension
import DGPS.Frontier.FIN068.Close

/-! Actual same-witness smooth flat chart for the FIN069 local lower estimate. -/

open MeasureTheory Filter Topology Set
open DGPS.Models DGPS.Frontier.FIN068 DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.FiniteN

/-- The single actual FIN068 witness admits a fixed smooth reduced extension, an exact
flat potential, and the actual Jacobian and metric bounds on one smaller chart. -/
theorem quartic_smooth_flat_chart :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ ∃ c ε δ : ℝ, 0 < c ∧ 0 < ε ∧ 0 < δ ∧
    ∃ v X : ℝ × ℝ → ℝ, ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧ (-4, 0) ∈ W ∧
      ContDiffOn ℝ ∞ v W ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (X q, q.2)) (Ioo (-ε) ε ×ˢ Ioo (-δ) δ) ∧
      (∀ p ∈ W, (v p, p.2) ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ) ∧
      (∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, (X q, q.2) ∈ W) ∧
      (∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, v (X q, q.2) = q.1) ∧
      (∀ p ∈ W, X (v p, p.2) = p.1) ∧
      (∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ,
        quarticPsi_FIN066 !₂[X q, q.2] = q.1 ^ 2 / 2 + Φ q.2) ∧
      (∀ y : ℝ, |y| < δ → deriv (deriv Φ) y ≤ -c * y ^ 2) ∧
      (∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ,
        1 / (2 * Real.sqrt quarticA_FIN06803) ≤
            (fderiv ℝ (fun z : ℝ × ℝ => (X z, z.2)) q).det ∧
          (fderiv ℝ (fun z : ℝ × ℝ => (X z, z.2)) q).det ≤
            2 / Real.sqrt quarticA_FIN06803) ∧
      (∀ q ∈ Ioo (-ε) ε ×ˢ Ioo (-δ) δ, ∀ ξ : Fin 2 → ℝ,
        sqnorm_FIN06836 ξ / (1 + 8 / quarticA_FIN06803) ≤
          sqnorm_FIN06836 ((Matrix.transpose
            (Matrix.of ![![fderiv ℝ v (X q, q.2) (1, 0),
              fderiv ℝ v (X q, q.2) (0, 1)], ![0, 1]])).mulVec ξ)) := by
  obtain ⟨hconstants, hweighted, δu, δz, hδu, hδz, a, ha, ha0, hacrit, hauniq, hda,
    hcurve, ρ, M₆, c, hρ, hM₆, hc, hred, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d,
    hφ, a₂, ha₂def, ha₂s, ha₂0, ha₂b, hfac, v, hvdef, hvs, hen, hv0, hvx, hvy,
    U, hUo, hU0, hUP, hUb, N, hNo, hN0, hNU, hinj, himgo, ε, δ, hε, hδ, hcl,
    X, hX, W, hWdef, hWo, hW0, hWN, hWb, hbij, hTs, hXs, hXW, hXv, hXinv,
    hder, hjac, hmetric, hneg⟩ := exact_negative_reduced_quartic_coefficient
  let φ : ℝ → ℝ := fun y => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y]
  obtain ⟨Φ, hΦ, hΦeq⟩ := quartic_reduced_extension δy hδy φ hφ
  let d : ℝ := min (δ / 2) (δy / 4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdδ : d ≤ δ := (min_le_left _ _).trans (by linarith)
  have hdδy : d < δy / 2 := (min_le_right _ _).trans_lt (by linarith)
  let Q : Set (ℝ × ℝ) := Ioo (-ε) ε ×ˢ Ioo (-d) d
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (v p, p.2)
  let W' : Set (ℝ × ℝ) := W ∩ T ⁻¹' Q
  have hQold : Q ⊆ Ioo (-ε) ε ×ˢ Ioo (-δ) δ :=
    Set.prod_mono (subset_refl _) (Ioo_subset_Ioo (neg_le_neg hdδ) hdδ)
  have hW'W : W' ⊆ W := inter_subset_left
  have hW'P : W' ⊆ Ioo (-4 - δx) (-4 + δx) ×ˢ Ioo (-δy) δy :=
    hW'W.trans (hWN.trans (hNU.trans hUP))
  have hW'o : IsOpen W' :=
    hTs.continuousOn.isOpen_inter_preimage hWo (isOpen_Ioo.prod isOpen_Ioo)
  have hW'0 : (-4, 0) ∈ W' := by
    refine ⟨hW0, ?_⟩
    change (v (-4, 0), (0 : ℝ)) ∈ Q
    rw [hv0]
    exact ⟨⟨by linarith, hε⟩, ⟨by linarith, hd⟩⟩
  have hRQ : ∀ q ∈ Q, (X q, q.2) ∈ W' := by
    intro q hq
    refine ⟨hXW q (hQold hq), ?_⟩
    change (v (X q, q.2), q.2) ∈ Q
    rw [hXv q (hQold hq)]
    exact hq
  refine ⟨Φ, hΦ, c, ε, d, hc, hε, hd, v, X, W', hW'o, hW'0,
    hvs.mono hW'P, hXs.mono hQold, fun p hp => hp.2, hRQ,
    fun q hq => hXv q (hQold hq), fun p hp => hXinv p hp.1, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hp := hXW q (hQold hq)
    have hy : |q.2| < δy / 2 := (abs_lt.mpr hq.2).trans hdδy
    have hext : Φ q.2 = φ q.2 := (hΦeq q.2 hy).eq_of_nhds
    rw [hen (X q) q.2 (hWN hp |> hNU |> hUP)]
    rw [hXv q (hQold hq), hext]
  · intro y hy
    have hq : ((0 : ℝ), y) ∈ Q := ⟨⟨by linarith, hε⟩, abs_lt.mp hy⟩
    have hcurv := (hneg (X (0, y), y) (hXW (0, y) (hQold hq))).2
    have hext := hΦeq y (hy.trans hdδy)
    rw [hext.deriv.deriv_eq]
    exact hcurv
  · intro q hq
    have hdX : DifferentiableAt ℝ X q :=
      (hX.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds (hQold hq))).differentiableAt (by simp)
    rw [quartic_inverse_chart_det X q hdX]
    exact hjac q (hQold hq)
  · intro q hq ξ
    exact (hmetric q (hQold hq) ξ).1

end DGPS.FiniteN
