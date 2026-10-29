import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.BoundedPerturbation
import SharpSymmetricLSI.Paper.CosineLabeled
import SharpSymmetricLSI.Paper.CosineMinimizer
import SharpSymmetricLSI.Paper.CosineSharpPoincare

/-!
# R39: Proposition 3.5 (`prop:cosine-labeled`), uniform full-labeled inequalities

Manuscript (3.28) and Proposition 3.5, (3.25)–(3.27), and Step 2 of its proof ((3.42)).
* (3.28) bounded perturbation (Holley–Stroock) on `𝕋^n`: for essentially bounded `ψ` and
  `dν ∝ e^{-ψ} dm^{⊗n}`, `Var_ν(u) ≤ (e^{ess sup ψ − ess inf ψ}/a) ∫ |∇u|² dν` for
  `u ∈ H^1(𝕋^n)`; the printed sup form is the corollary `bounded_perturbation_poincare_sup`.
* (3.25) `λ^all_{N,κ} ≥ a max{e^{-κN/2}, e^{-2κ} - κ/N}` for `N ≥ 1`.
* (3.26) `r^all_{N,κ} ≥ 2aλ^all_{N,κ}/(4λ^all_{N,κ} + (2κ+8)a)`.
* (3.27) `inf_{N≥1} λ^all_{N,κ} ≥ a min{e^{-2κ}/2, exp(-κ² e^{2κ})} > 0`, and
  `inf_{N≥1} r^all_{N,κ} > 0`.
* Step 2: the infimum (3.24) is attained by a mean-zero, `L²`-normalized
  `φ ∈ H^1(P_{N,κ}) ∩ H^2(𝕋^N)` solving (3.42) weakly against smooth test functions.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

/-- (3.28), with `ess sup ψ - ess inf ψ` in place of `sup ψ - inf ψ` (Matt's choice at sign-off,
2026-10-03): the bounded-perturbation Poincaré inequality on `𝕋^n` for essentially bounded `ψ`. -/
theorem bounded_perturbation_poincare {n : ℕ} {ψ : UnitAddTorus (Fin n) → ℝ}
    (hψ : AEMeasurable ψ volume)
    (hb : ∃ B, ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin n))), |ψ x| ≤ B)
    {u : UnitAddTorus (Fin n) → ℝ} (hu : MemH1 volume u) :
    let ν : Measure (UnitAddTorus (Fin n)) := volume.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-ψ x) / ∫ y, Real.exp (-ψ y)))
    var ν u ≤ ENNReal.ofReal (Real.exp (essSup ψ volume - essInf ψ volume) / aCos) *
      dirichlet ν u := by
  exact bounded_perturbation_aux hψ hb hu

/-- (3.28) as printed (pointwise `sup`, `inf`, bounded measurable `ψ`); a corollary of
`bounded_perturbation_poincare` since `essSup ψ ≤ ⨆ x, ψ x` and `⨅ x, ψ x ≤ essInf ψ`. -/
theorem bounded_perturbation_poincare_sup {n : ℕ} {ψ : UnitAddTorus (Fin n) → ℝ}
    (hψ : Measurable ψ) (hb : ∃ B, ∀ x, |ψ x| ≤ B) {u : UnitAddTorus (Fin n) → ℝ}
    (hu : MemH1 volume u) :
    let ν : Measure (UnitAddTorus (Fin n)) := volume.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-ψ x) / ∫ y, Real.exp (-ψ y)))
    var ν u ≤ ENNReal.ofReal (Real.exp ((⨆ x, ψ x) - ⨅ x, ψ x) / aCos) * dirichlet ν u := by
  exact bounded_perturbation_sup_aux hψ hb hu

/-- (3.25). -/
theorem cosine_labeled_poincare {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    ENNReal.ofReal (aCos * max (Real.exp (-κ * N / 2)) (Real.exp (-2 * κ) - κ / N)) ≤
      lamAll cosV (cosW κ) N := by
  exact cosine_labeled_poincare_aux hκ hN

/-- (3.26). -/
theorem cosine_labeled_lsi {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    2 * ENNReal.ofReal aCos * lamAll cosV (cosW κ) N /
        (4 * lamAll cosV (cosW κ) N + ENNReal.ofReal ((2 * κ + 8) * aCos)) ≤
      rAll cosV (cosW κ) N := by
  exact rAll_ge_of_lamAll hκ hN

/-- (3.27) and `inf_{N≥1} r^all_{N,κ} > 0`. -/
theorem cosine_uniform_all {κ : ℝ} (hκ : 0 < κ) :
    ENNReal.ofReal (aCos * min (Real.exp (-2 * κ) / 2) (Real.exp (-κ ^ 2 * Real.exp (2 * κ))))
        ≤ ⨅ N ∈ {N : ℕ | 1 ≤ N}, lamAll cosV (cosW κ) N ∧
      0 < aCos * min (Real.exp (-2 * κ) / 2) (Real.exp (-κ ^ 2 * Real.exp (2 * κ))) ∧
      0 < ⨅ N ∈ {N : ℕ | 1 ≤ N}, rAll cosV (cosW κ) N := by
  exact cosine_uniform_all_aux hκ

/-- Step 2 of the proof of Proposition 3.5: the infimum (3.24) is attained by an `H^2` function
solving the weak eigenvalue equation (3.42). -/
theorem cosine_gap_minimizer {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ φ : Config N 1 → ℝ, MemH1C (gibbs cosV (cosW κ) N) φ ∧
      ∫ X, φ X ∂gibbs cosV (cosW κ) N = 0 ∧ ∫ X, φ X ^ 2 ∂gibbs cosV (cosW κ) N = 1 ∧
      energy cosV (cosW κ) N φ = lamAll cosV (cosW κ) N ∧ MemH2C φ ∧
      ∀ η : Config N 1 → ℝ, IsSmoothC η →
        ∫ X, ∑ i, weakGradC φ X i 0 * cpartialC η i 0 X =
          ∫ X, ((lamAll cosV (cosW κ) N).toReal * φ X -
            ∑ i, cpartialC (cosU κ N) i 0 X * weakGradC φ X i 0) * η X := by
  exact cosine_gap_minimizer_aux hκ hN

end SharpLSI
