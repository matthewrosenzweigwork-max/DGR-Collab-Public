import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Infra.Classical
import SharpSymmetricLSI.Paper.RefSpectrum17

/-!
# R23: (6.1), the reference spectrum

Manuscript (6.1) and the paragraph after it. Assume (1.2), `r_* > 0`, `μ` the minimizer.
A reference eigenbasis exists; for every such basis `0 < λ_1 ≤ λ_2 ≤ …` and `λ_j ≥ c j^{2/d}`
(`j ≥ 1`); every `e_j` is in `W^{2,p}` for every finite `p` (second weak derivatives in
`L^p(m)`), has a `C^1` representative whose derivatives are `α`-Hölder for every `α < 1`, and
the `C^1` norms grow at most polynomially in `1 + λ_j`.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- (6.1). -/
theorem ref_spectrum {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    (∃ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam) ∧
    ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      (∀ j, 1 ≤ j → 0 < lam j) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      (∀ j (p : ℝ≥0∞), p ≠ ⊤ → ∀ k, HasWeakGrad (fun x => weakGrad (e j) x k) ∧
        ∀ l, MemLp (fun x => weakGrad (fun y => weakGrad (e j) y k) x l) p (haar d)) ∧
      ∃ (C : ℝ) (q : ℕ), ∀ j, ∃ eC : Torus d → ℝ,
        ContDiff ℝ 1 (eC ∘ liftT) ∧ eC =ᵐ[(μ : Measure (Torus d))] e j ∧
        (∀ x, |eC x| + Real.sqrt (sqNorm fun k => cpartial eC k x) ≤ C * (1 + lam j) ^ q) ∧
        ∀ α : NNReal, α < 1 → ∃ H : NNReal, ∀ k, HolderWith H α (fun x => cpartial eC k x) :=
  ref_spectrum_aux hd hyp hμ

end SharpLSI
