import SharpSymmetricLSI.Paper.Prop23Assembly2
import SharpSymmetricLSI.Paper.GaussLSI6

/-!
# Proposition 2.3 (R04) from the form hypothesis alone

`prop_compactness_of_form`: `prop_compactness_of` with its inputs `hLSI` (R32 `gaussian_lsi`, via
`gaussian_lsi_of_prop21`, `Paper/GaussLSI6.lean`) and `hlam` ((2.8), via `lamSym_tendsto_of''`,
`Paper/GaussPoincare3.lean`) discharged; the only remaining hypothesis is the compactness
property `hform` ((8.20), (2.5)–(2.7), R33).

This file does not import Statements R01, R04, R07, R08 or R33.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **Proposition 2.3 from the form hypothesis.** -/
theorem prop_compactness_of_form (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (hform : ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      ∀ C, IsInverseOfIPlus (Tmat W μ e) C → ∀ γ, IsCenteredGaussianCov γ C →
        CompactnessProperty' V W γ (gaussForm (lamShift lam) γ)) :
    CompactnessConclusion' V W :=
  prop_compactness_of hd hyp hr
    (fun _ hμ _ _ he _ hC _ hγ => gaussian_lsi_of_prop21 hd hyp hr hμ he hC hγ) hform
    (fun μ hμ e lam he C hC γ hγ =>
      (lamSym_tendsto_of'' hd hyp hr hμ he hC hγ (hform μ hμ e lam he C hC γ hγ)).2.2)

end SharpLSI
