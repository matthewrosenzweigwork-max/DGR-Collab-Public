import FullLabeledLSI.Paper.Sec5Pinsker
import FullLabeledLSI.Paper.Sec5Birthday

/-!
# Lemma 5.5 (conditional force comparison): abstract setting

For measurable bounded `bF : 𝕋^d → 𝕋^d → Fin d → ℝ` (a representative of `b = ∇₁K`) and
`bΔ : 𝕋^d → Fin d → ℝ` (a representative of `b_Δ`), the conditional mean force
`B_S(X, x) = ∫ b(x,y) dρ̄_S(y)` and the particle force
`G_{i,k}(X) = N⁻¹ (∑_{l ≠ i} b(X_i, X_l) + b_Δ(X_i))`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- Real-valued uniform average over a `j`-subset `S` and a label `i ∈ Sᶜ`. -/
noncomputable def avg1R (N j : ℕ) (F : Finset (Fin N) → Fin N → ℝ) : ℝ :=
  ((Nat.choose N j : ℝ)⁻¹) * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, F S i

/-- `B_{S,k}(X, x) = ∫ b_k(x,y) dρ̄_S(y)`. -/
noncomputable def BS (bF : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d))
    [IsFiniteMeasure ν] (S : Finset (Fin N)) (X : Config N d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, bF x y k ∂barCond ν S X

/-- `G_{i,k}(X) = N⁻¹ (∑_{l ≠ i} b_k(X_i, X_l) + b_Δ,k(X_i))`. -/
noncomputable def Gpart (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ) (N : ℕ)
    (X : Config N d) (i : Fin N) (k : Fin d) : ℝ :=
  (N : ℝ)⁻¹ * ((∑ l, if l ≠ i then bF (X i) (X l) k else 0) + bΔ (X i) k)

/-- `E |B_S(X_I) - G_I|²` at level `j`. -/
noncomputable def forceDelta (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ)
    (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j : ℕ) : ℝ :=
  avg1R N j fun S i => ∫ X, ∑ k : Fin d, (BS bF ν S X (X i) k - Gpart bF bΔ N X i k) ^ 2 ∂ν

/-- The test `A₃(x,y,z) = b(x,y)·b(x,z)`. -/
noncomputable def A3 (bF : Torus d → Torus d → Fin d → ℝ) : (Fin 3 → Torus d) → ℝ :=
  fun z => ∑ k : Fin d, bF (z 0) (z 1) k * bF (z 0) (z 2) k

/-- The standing assumptions on the representatives. -/
structure ForceRep (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ) (Bb : ℝ) :
    Prop where
  meas : ∀ k, Measurable fun p : Torus d × Torus d => bF p.1 p.2 k
  measΔ : ∀ k, Measurable fun x => bΔ x k
  bound : ∀ x y k, |bF x y k| ≤ Bb
  boundΔ : ∀ x k, |bΔ x k| ≤ Bb

end SharpLSI.FL
