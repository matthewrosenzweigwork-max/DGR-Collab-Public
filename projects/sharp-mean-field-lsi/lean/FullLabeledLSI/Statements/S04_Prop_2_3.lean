import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D13_Equilibrium
import FullLabeledLSI.Paper.Prop23HAltB
import FullLabeledLSI.Paper.Prop23HAltNs

/-!
# S4: Proposition 2.3 (`prop:bounded`), bounded-observable comparison

Manuscript Proposition 2.3, (2.3), (2.4). Assume (1.2) and `r_* > 0`. Let `μ` be the equilibrium,
`λ_G` the Gaussian rate, `b = min{r_LS(μ), λ_G}` (1.21). For every sequence of real `f_N ∈ H^1(P_N)`
with `sup_N (‖f_N‖_∞ + ℰ_N(f_N)) < ∞`,
`liminf_N (ℰ_N(f_N) - (b/2) Ent_{P_N}(f_N²)) ≥ 0`; the same holds along any subsequence of particle
numbers tending to infinity.

Encodings (following R4 of the symmetric project): `λ_G = lamG (lamShift lam) C` for every reference
eigenbasis `(e, lam)` of `μ` (D16) and every `C` with `IsInverseOfIPlus (Tmat W μ e) C`; the
statement is made for every minimizer `μ` (it is unique when `r_* > 0`). Sequences are indexed by
`k` with particle numbers `Ns k → ∞` (this contains both the full sequence and every subsequence).
`‖f‖_∞` is the essential supremum under `P_N`. `liminf ≥ 0` is written
`∀ ε > 0, eventually (b/2) Ent ≤ ℰ + ε`; both sides are finite under the hypotheses.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The bounded-observable comparison at rate `b` (2.4), along particle numbers `Ns k → ∞`. -/
def BoundedComparison (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (b : ℝ≥0∞) : Prop :=
  ∀ (Ns : ℕ → ℕ), Tendsto Ns atTop atTop → ∀ f : (k : ℕ) → Config (Ns k) d → ℝ,
    (∀ k, MemH1C (gibbs V W (Ns k)) (f k)) →
    (∃ B : NNReal, ∀ k, (∀ᵐ X ∂gibbs V W (Ns k), |f k X| ≤ B) ∧
      energy V W (Ns k) (f k) ≤ B) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      b / 2 * ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≤
        energy V W (Ns k) (f k) + ENNReal.ofReal ε

/-- Proposition 2.3. -/
theorem prop_bounded {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    BoundedComparison V W (bRate (μ : Measure (Torus d)) lam C) := by
  exact boundedComparison_unfolded hyp (propBoundedCore_alt hd hyp hr μ hμ e lam he C hC)

end SharpLSI.FL
