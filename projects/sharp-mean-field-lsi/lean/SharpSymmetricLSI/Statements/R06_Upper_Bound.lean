import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Paper.ProductEntropy
import SharpSymmetricLSI.Paper.SemiconvexHyp
import SharpSymmetricLSI.Paper.ProductFisherMain
import SharpSymmetricLSI.Paper.UpperComparison
import SharpSymmetricLSI.Paper.UpperBound

/-!
# R6: Section 2.2 (`sec:upper`), product-state identities and the upper bound

Manuscript Section 2.2, (2.10)–(2.12). Fix a smooth positive probability density `ρ` with
`G(ρ) > 0` and put `ν_N = ρ^{⊗N}`, `f_N = √(dν_N/dP_N)`.
* (2.10): `N^{-1} H(ν_N|P_N) = H(ρ|m) + ρ(V) + ((N-1)/(2N)) W(ρ,ρ) + N^{-1} log Z_N → G(ρ)`.
* (2.11): with `b_ρ(x) = ∫ ∇₁W(x,y) dρ(y)`,
  `N^{-1} I(ν_N|P_N) = ∫ |∇log ρ + ∇V + ((N-1)/N) b_ρ|² dρ
     + ((N-1)/N²) ∫ (∫ |∇₁W(x,y)|² dρ(y) - |b_ρ(x)|²) dρ(x) → D(ρ)`.
* `4 ℰ_N(f_N) = I(ν_N|P_N)`, and (2.12): `limsup_N r_N^sym ≤ D(ρ)/(2G(ρ))`.
* Taking the infimum over `ρ`: `limsup_N r_N^sym ≤ r_*`; if `r_* = 0`, `r_N^sym → 0`.

`∇₁W(x,y)` is the weak gradient of the Lipschitz function `W` on `(𝕋^d)²` in the first
variable (`grad1W`). All identities are for `N ≥ 1`.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- `∇₁W(x,y)`: the weak gradient of `(x,y) ↦ W(x,y)` on `(𝕋^d)²` in the first variable. -/
noncomputable def grad1W (W : Torus d → Torus d → ℝ) (x y : Torus d) (k : Fin d) : ℝ :=
  weakGradC (fun X : Config 2 d => W (X 0) (X 1)) ![x, y] 0 k

/-- `b_ρ(x) = ∫ ∇₁W(x,y) dρ(y)` for a density `ρ`. -/
noncomputable def forceDens (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (x : Torus d)
    (k : Fin d) : ℝ :=
  ∫ y, grad1W W x y k * ρ y ∂haar d

/-- A smooth positive probability density with positive gap (the test class of Section 2.2). -/
def IsProductTest (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) : Prop :=
  IsSmoothT ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x ∂haar d = 1 ∧ 0 < gap V W (densMeasure ρ)

/-- The product state `ν_N = ρ^{⊗N}`. -/
noncomputable def productState (ρ : Torus d → ℝ) (N : ℕ) : Measure (Config N d) :=
  Measure.pi (fun _ : Fin N => densMeasure ρ)

/-- (2.10): the entropy identity and its limit. -/
theorem product_state_entropy {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ : IsProductTest V W ρ) :
    (∀ N : ℕ, 1 ≤ N →
      klDiv (productState ρ N) (gibbs V W N) ≠ ⊤ ∧
      (klDiv (productState ρ N) (gibbs V W N)).toReal / N =
        (klDiv (densMeasure ρ) (haar d)).toReal + potE V (densMeasure ρ) +
          ((N : ℝ) - 1) / (2 * N) * interE W (densMeasure ρ) (densMeasure ρ) +
          Real.log (partitionFn V W N) / N) ∧
    gap V W (densMeasure ρ) ≠ ⊤ ∧
    Tendsto (fun N : ℕ => (klDiv (productState ρ N) (gibbs V W N)).toReal / N) atTop
      (𝓝 (gap V W (densMeasure ρ)).toReal) := by
  exact product_state_entropy_aux hyp hρ.1 hρ.2.1 hρ.2.2.1

/-- (2.11): the Fisher-information identity and its limit, and `4ℰ_N(f_N) = I(ν_N|P_N)`. -/
theorem product_state_fisher {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ : IsProductTest V W ρ) :
    (∀ N : ℕ, 1 ≤ N →
      fisherInfoC (productState ρ N) (gibbs V W N) ≠ ⊤ ∧
      (fisherInfoC (productState ρ N) (gibbs V W N)).toReal / N =
        (∫ x, sqNorm (fun k => weakGrad (fun y => Real.log (ρ y)) x k + weakGrad V x k +
            ((N : ℝ) - 1) / N * forceDens W ρ x k) ∂densMeasure ρ) +
          ((N : ℝ) - 1) / (N : ℝ) ^ 2 *
            ∫ x, ((∫ y, sqNorm (grad1W W x y) ∂densMeasure ρ) - sqNorm (forceDens W ρ x))
              ∂densMeasure ρ ∧
      4 * energy V W N
          (fun X => Real.sqrt ((productState ρ N).rnDeriv (gibbs V W N) X).toReal) =
        fisherInfoC (productState ρ N) (gibbs V W N)) ∧
    dissipation V W ρ ≠ ⊤ ∧
    Tendsto (fun N : ℕ => (fisherInfoC (productState ρ N) (gibbs V W N)).toReal / N) atTop
      (𝓝 (dissipation V W ρ).toReal) := by
  exact product_state_fisher_aux hyp hρ.1 hρ.2.1 hρ.2.2.1

/-- (2.12): the product-state upper comparison. -/
theorem upper_comparison {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ : IsProductTest V W ρ) :
    limsup (fun N => rSym V W N) atTop ≤
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal) := by
  exact upper_comparison_aux hyp hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2

/-- Section 2.2: `limsup_N r_N^sym ≤ r_*` (no assumption `r_* > 0`). -/
theorem upper_bound {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    limsup (fun N => rSym V W N) atTop ≤ rStar V W := by
  exact upper_bound_aux hyp

/-- Section 2.2, the zero-rate case: if `r_* = 0` then `r_N^sym → 0 = r_*`. -/
theorem zero_rate {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (h0 : rStar V W = 0) :
    Tendsto (fun N => rSym V W N) atTop (𝓝 0) := by
  exact zero_rate_aux hyp h0

end SharpLSI
