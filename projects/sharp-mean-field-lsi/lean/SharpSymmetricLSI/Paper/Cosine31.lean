import SharpSymmetricLSI.Paper.CosineRemark39
import SharpSymmetricLSI.Paper.CosineSharpPoincare
import SharpSymmetricLSI.Paper.CosineStrict
import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Paper.CosineHyp
import SharpSymmetricLSI.Paper.CosineTagged

/-!
# R08 (Proposition 3.1): assembly, conditional on Theorem 1.1 at the cosine instance

All clauses of Proposition 3.1 are proved in Section 3 (R09, R12, R39, R43, CosineExpansion)
except `r^sym_{N,κ} → r_{*,κ}`, which is Theorem 1.1 (1.9) for the cosine model; it is taken as the
hypothesis `hlim` of `prop_cosine_of`. The uniform lower bound `inf_N r^all_{N,κ} > 0` combines
`λ^all_{N,κ} ≥ a e^{-2κ}/2` for `N ≥ 2κe^{2κ}` (R43) with `λ^all_{N,κ} ≥ a e^{-κN/2}` (R39) for the
finitely many smaller `N`, and `r^all ≥ 2ac/(4c+b)` for `c ≤ λ^all` (`rAll_ge_of_lam_ge`).
-/

open Filter Topology Real

namespace SharpLSI

theorem lamAll_ge_uniform {κ : ℝ} (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ENNReal.ofReal c ≤ lamAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  set N0 : ℝ := 2 * κ * exp (2 * κ)
  refine ⟨aCos * min (exp (-2 * κ) / 2) (exp (-κ * N0 / 2)), by positivity, fun N hN => ?_⟩
  by_cases hNκ : N0 ≤ N
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (cosine_labeled_constants_aux hκ hN hNκ).1
    have h := mul_le_mul_of_nonneg_left (min_le_left (exp (-2 * κ) / 2) (exp (-κ * N0 / 2))) ha0.le
    calc _ ≤ aCos * (exp (-2 * κ) / 2) := h
      _ = aCos * exp (-2 * κ) / 2 := by ring
  · push_neg at hNκ
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (cosine_labeled_poincare_aux hκ hN)
    refine mul_le_mul_of_nonneg_left ((min_le_right _ _).trans ((exp_le_exp.mpr ?_).trans
      (le_max_left _ _))) ha0.le
    nlinarith

/-- **Proposition 3.1**, conditional on `r^sym_{N,κ} → r_{*,κ}` (Theorem 1.1 at the cosine model). -/
theorem prop_cosine_of {κ : ℝ} (hκ : 0 < κ)
    (hlim : Tendsto (fun N => rSym cosV (cosW κ) N) atTop (𝓝 (rStar cosV (cosW κ)))) :
    (∃ KV KW : ℝ, Hyp cosV (cosW κ) KV KW) ∧
    0 < ⨅ N ∈ {N : ℕ | 1 ≤ N}, rAll cosV (cosW κ) N ∧
    (∀ N : ℕ, 1 ≤ N → rAll cosV (cosW κ) N ≤ ENNReal.ofReal aCos) ∧
    ENNReal.ofReal aCos < rStar cosV (cosW κ) ∧
    Tendsto (fun N => rSym cosV (cosW κ) N) atTop (𝓝 (rStar cosV (cosW κ))) ∧
    rStar cosV (cosW κ) ≤ ENNReal.ofReal (aCos * min (1 + κ / 2) 4) := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  obtain ⟨c, hc0, hc⟩ := lamAll_ge_uniform hκ
  refine ⟨⟨0, 2 * aCos * κ, cosine_hyp_aux hκ⟩, ?_, fun N hN => cosine_rAll_le_aux hN,
    cosine_strict_aux hκ, hlim, cosine_rStar_le_aux hκ⟩
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (show 0 < 2 * aCos * c /
    (4 * c + (2 * κ + 8) * aCos) by positivity)) (le_iInf₂ fun N hN => ?_)
  exact rAll_ge_of_lam_ge hκ hN hc0 (hc N hN)

end SharpLSI
