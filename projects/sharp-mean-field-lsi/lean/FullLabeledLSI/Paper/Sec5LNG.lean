import SharpSymmetricLSI.Paper.Defective29

/-!
# Large-N assembly G: the real algebra
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 7. L5: the real algebra -/

/-- The explicit constant of `large_N_reg_all`: with `α = 2r₀(1-(2+4AC20)τ)`, `β = 1+ε+8r₀Aτ`,
`q = √C19`, `K₁ = 2r₀(4τA·C20 + CK + C18) + (1+1/ε)C21`, `K₂ = (2r₀C18 + (1+1/ε)C21) q`:
`algK = max 0 (K₁ + (α - 2rβ) + K₂²/(4(α - 2rβ)))`. -/
noncomputable def algK (r r₀ τ ε A C18 C19 C20 C21 CK : ℝ) : ℝ :=
  max 0 ((2 * r₀ * (4 * τ * A * C20 + CK + C18) + (1 + 1 / ε) * C21) +
    (2 * r₀ * (1 - (2 + 4 * A * C20) * τ) - 2 * r * (1 + ε + 8 * r₀ * A * τ)) +
    ((2 * r₀ * C18 + (1 + 1 / ε) * C21) * Real.sqrt C19) ^ 2 /
      (4 * (2 * r₀ * (1 - (2 + 4 * A * C20) * τ) - 2 * r * (1 + ε + 8 * r₀ * A * τ))))

/-- **L5.  The algebra of the large-`N` estimate** (pure real arithmetic; this is the second half of
`Defective28.large_N_reg`, `hP1`–`hfinal`, followed by `absorb_sqrt`).  Notation: `H = H(ν|P_N)`,
`H0 = H(ν|μ^N)`, `I = Σ E|s_i|²`, `GG = E|∇U_N|²`, `EU = E_ν U_N`, `L = log K_N`,
`Sh = Σ_{j<ℓ} h_j`, `Scp = Σ_{j<ℓ} cps_j`, `Sf = Σ_{j<ℓ} forceDelta_j`, `P = M h_{N-1}`, `m = M/N`.
Hypotheses are exactly the real inequalities delivered by `level_bound` (summed, `ℓ/N ≤ 1`), the force sum,
`chain_lower`, `hRev_toReal_le` + `sum_sG_le` (`P ≤ m A (2I + 2GG)`), `products_J`, the entropy identity,
`reference_all_aux`, `reference_entropy`.  Proof: `Sh + Scp ≥ (1-2τ)H - 2τA(2I+2C20(H+1)) - CK - C18(1+√H0)`,
`√H0 ≤ √C19 √(H+1)`, multiply by `2r₀`, add `hmain`, get `αH ≤ βI + K₁ + K₂√(H+1)`, then
`SharpLSI.absorb_sqrt`.  ~60 lines. -/
theorem large_N_algebra {r r₀ τ ε A C18 C19 C20 C21 CK : ℝ}
    (hr : 0 < r) (hrr₀ : r < r₀) (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 4) (hε : 0 < ε) (hA : 0 ≤ A)
    (hC18 : 0 ≤ C18) (hC19 : 0 ≤ C19) (hC20 : 0 ≤ C20) (hC21 : 0 ≤ C21) (hCK : 0 ≤ CK)
    (hchoice : 2 * r * (1 + ε + 8 * r₀ * A * τ) < 2 * r₀ * (1 - (2 + 4 * A * C20) * τ))
    {H H0 I GG EU L Sh Scp Sf P m : ℝ}
    (hH : 0 ≤ H) (hH0 : 0 ≤ H0) (hI : 0 ≤ I) (hGG : 0 ≤ GG) (hm0 : 0 ≤ m) (hm2 : m ≤ 2 * τ)
    (hmain : 2 * r₀ * (Sh + Scp) ≤ (1 + ε) * I + (1 + 1 / ε) * Sf)
    (hSf : Sf ≤ C21 * (1 + Real.sqrt H0))
    (hSh : H0 - P ≤ Sh)
    (hP : P ≤ m * A * (2 * I + 2 * GG))
    (hScp : (1 - m) * EU - C18 * (1 + Real.sqrt H0) ≤ Scp)
    (hEU : EU = H - H0 - L) (hL : L ≤ CK)
    (hH0le : H0 ≤ C19 * (H + 1)) (hGGle : GG ≤ C20 * (H + 1)) :
    2 * r * H ≤ I + algK r r₀ τ ε A C18 C19 C20 C21 CK := by
  have hr₀ : 0 < r₀ := hr.trans hrr₀
  have hs0 : Real.sqrt H0 ≤ Real.sqrt C19 * Real.sqrt (H + 1) := by
    rw [← Real.sqrt_mul hC19]; exact Real.sqrt_le_sqrt hH0le
  have hs0nn : 0 ≤ Real.sqrt H0 := Real.sqrt_nonneg _
  have h1m : 0 ≤ 1 - m := by linarith
  have hQ1 : (1 - 2 * τ) * H ≤ (1 - m) * H := mul_le_mul_of_nonneg_right (by linarith) hH
  have hQ2 : (1 - m) * L ≤ CK := by
    calc (1 - m) * L ≤ (1 - m) * CK := mul_le_mul_of_nonneg_left hL h1m
      _ ≤ CK := by have := mul_nonneg hm0 hCK; linarith
  have hQ3 : 0 ≤ m * H0 := mul_nonneg hm0 hH0
  have hP1 : P ≤ 2 * τ * A * (2 * I + 2 * (C20 * (H + 1))) := by
    have h2 : m * A * (2 * I + 2 * GG) ≤ 2 * τ * A * (2 * I + 2 * (C20 * (H + 1))) := by
      have : 2 * I + 2 * GG ≤ 2 * I + 2 * (C20 * (H + 1)) := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_right hm2 hA) this (by linarith)
        (by have := hτ0.le; positivity)
    linarith
  have hEUe : (1 - m) * EU = (1 - m) * H - (1 - m) * H0 - (1 - m) * L := by
    rw [hEU]; ring
  have hlow : (1 - 2 * τ) * H - 2 * τ * A * (2 * I + 2 * (C20 * (H + 1))) - CK -
      C18 * (1 + Real.sqrt H0) ≤ Sh + Scp := by
    nlinarith only [hSh, hScp, hP1, hQ1, hQ2, hQ3, hEUe]
  have hlow2 := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * r₀)
  have hSf' : (1 + 1 / ε) * Sf ≤ (1 + 1 / ε) * (C21 * (1 + Real.sqrt H0)) :=
    mul_le_mul_of_nonneg_left hSf (by positivity)
  have hK₂0 : 0 ≤ (2 * r₀ * C18 + (1 + 1 / ε) * C21) * Real.sqrt C19 := by positivity
  have hcoef : 0 ≤ 2 * r₀ * C18 + (1 + 1 / ε) * C21 := by positivity
  have hs0' := mul_le_mul_of_nonneg_left hs0 hcoef
  have hfinal : (2 * r₀ * (1 - (2 + 4 * A * C20) * τ)) * H ≤
      (1 + ε + 8 * r₀ * A * τ) * I +
        (2 * r₀ * (4 * τ * A * C20 + CK + C18) + (1 + 1 / ε) * C21) +
        ((2 * r₀ * C18 + (1 + 1 / ε) * C21) * Real.sqrt C19) * Real.sqrt (H + 1) := by
    nlinarith only [hlow2, hmain, hSf', hs0']
  have := SharpLSI.absorb_sqrt hr (by nlinarith [mul_nonneg hr₀.le (mul_nonneg hA hτ0.le)] :
      (1 : ℝ) ≤ 1 + ε + 8 * r₀ * A * τ) hchoice hK₂0 hH hfinal
  exact this


end SharpLSI.FL
