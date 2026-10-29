import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D18_GaussianForm

/-!
# Proposition 2.3: a definitional copy of `CompactnessProperty`

`CompactnessProperty'` is `CompactnessProperty` of Statements/R04, defined here so that Paper
lemmas proving it (Section 8, R33) and the assembly of Proposition 2.3 (Paper/Prop23Assembly) do
not import the statement files R04 or R33 (R33 imports R04). The bridge
`compactnessProperty'_eq` (Paper/Prop23Bridge) is `rfl`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- A definitional copy of `CompactnessProperty` (Statements/R04): the compactness statement
(2.5)–(2.7) of Proposition 2.3 for a given `γ_∞` and `ℰ_∞`. -/
def CompactnessProperty' (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (γ : Measure (ℕ → ℝ))
    (EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞) : Prop :=
  ∀ (Ns : ℕ → ℕ), Tendsto Ns atTop atTop → ∀ f : (k : ℕ) → Config (Ns k) d → ℝ,
    (∀ k, MemH1C (gibbs V W (Ns k)) (f k) ∧ IsSymmetric (f k)) →
    (∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k)) + energy V W (Ns k) (f k) ≤ B) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ ∧
      (∀ g : ℝ →ᵇ ℝ, Tendsto (fun k => ∫ X, g (f (φ k) X) ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, g (F z) ∂γ))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
        ∫⁻ X in {X | M < f (φ k) X ^ 2}, ENNReal.ofReal (f (φ k) X ^ 2) ∂gibbs V W (Ns (φ k))
          ≤ ENNReal.ofReal ε) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ∂gibbs V W (Ns (φ k))) atTop (𝓝 (∫ z, F z ∂γ)) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ^ 2 ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, F z ^ 2 ∂γ)) ∧
      EInf F ≤ liminf (fun k => energy V W (Ns (φ k)) (f (φ k))) atTop ∧
      ∀ χ : ℝ → ℝ, (∃ L, LipschitzWith L χ) →
        EInf (χ ∘ F) ≤ liminf (fun k => energy V W (Ns (φ k)) (χ ∘ f (φ k))) atTop

end SharpLSI
