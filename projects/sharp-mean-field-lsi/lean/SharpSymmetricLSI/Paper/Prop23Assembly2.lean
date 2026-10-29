import SharpSymmetricLSI.Paper.Prop23Assembly1
import SharpSymmetricLSI.Paper.Prop23Defs
import SharpSymmetricLSI.Paper.ULimit4
import SharpSymmetricLSI.Statements.R23_Reference_Spectrum
import SharpSymmetricLSI.Statements.R27_Lemma_6_1

/-!
# Proposition 2.3 (lane s42; R04): assembly

`prop_compactness_of`: the conclusion of Proposition 2.3 (concrete form), with the Section 8
inputs as hypotheses:
* `hLSI`: (8.9), (8.10), (8.13) (R32 `gaussian_lsi`);
* `hform`: (8.20), (2.5)–(2.7) (R33 `form_liminf`, as `CompactnessProperty'`);
* `hlam`: (2.8) `λ_N^sym → λ_G` (R33 `lamSym_tendsto`).
The existence clauses come from R23 (reference eigenbasis), Paper/Prop23Assembly1 (`C`), and
R27 (`γ_∞` with covariance `C`).

`GaussianInputProperties'` and `CompactnessConclusion'` are definitional copies of R04's
`GaussianInputProperties` and `CompactnessConclusion` (this file must not import R04, whose
proof will import it). This file does not import Statements R01, R03, R04 or R33.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A definitional copy of `GaussianInputProperties` (Statements/R04). -/
def GaussianInputProperties' (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (γ : Measure (ℕ → ℝ)) (EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞) (lG : ℝ≥0∞) : Prop :=
  rStar V W ≤ lG ∧
  (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
    ent γ (fun z => f z ^ 2) ≤ 2 / lG * EInf f ∧ var γ f ≤ EInf f / lG) ∧
  CompactnessProperty' V W γ EInf ∧
  Tendsto (fun N => lamSym V W N) atTop (𝓝 lG)

/-- A definitional copy of `CompactnessConclusion` (Statements/R04). -/
def CompactnessConclusion' (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
    (∃ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam) ∧
    ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      (∃ C, IsInverseOfIPlus (Tmat W μ e) C) ∧
      ∀ C, IsInverseOfIPlus (Tmat W μ e) C →
        (∃ γ, IsCenteredGaussianCov γ C) ∧
        ∀ γ, IsCenteredGaussianCov γ C →
          GaussianInputProperties' V W γ (gaussForm (lamShift lam) γ) (lamG (lamShift lam) C)

/-- **Proposition 2.3** from the Section 8 inputs. -/
theorem prop_compactness_of (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (hLSI : ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      ∀ C, IsInverseOfIPlus (Tmat W μ e) C → ∀ γ, IsCenteredGaussianCov γ C →
        0 < lamG (lamShift lam) C ∧ lamG (lamShift lam) C < ⊤ ∧
        (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
          ent γ (fun z => f z ^ 2) ≤ 2 / lamG (lamShift lam) C * gaussForm (lamShift lam) γ f ∧
          var γ f ≤ gaussForm (lamShift lam) γ f / lamG (lamShift lam) C) ∧
        rStar V W ≤ lamG (lamShift lam) C)
    (hform : ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      ∀ C, IsInverseOfIPlus (Tmat W μ e) C → ∀ γ, IsCenteredGaussianCov γ C →
        CompactnessProperty' V W γ (gaussForm (lamShift lam) γ))
    (hlam : ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      ∀ C, IsInverseOfIPlus (Tmat W μ e) C → ∀ γ, IsCenteredGaussianCov γ C →
        Tendsto (fun N => lamSym V W N) atTop (𝓝 (lamG (lamShift lam) C))) :
    CompactnessConclusion' V W := by
  intro μ hμ
  refine ⟨(ref_spectrum hd hyp hr hμ).1, fun e lam he => ?_⟩
  refine ⟨exists_inverseOfIPlus hyp μ hd hr hμ he, fun C hC => ?_⟩
  refine ⟨?_, fun γ hγ => ?_⟩
  · obtain ⟨Q, hQ⟩ := exists_secondChaos_Tmat hyp hμ he
    exact ⟨_, (gaussian_limit_law hd hyp hr hμ he hQ hC).2.2.1⟩
  · obtain ⟨-, -, hG, hrG⟩ := hLSI μ hμ e lam he C hC γ hγ
    exact ⟨hrG, hG, hform μ hμ e lam he C hC γ hγ, hlam μ hμ e lam he C hC γ hγ⟩

end SharpLSI
