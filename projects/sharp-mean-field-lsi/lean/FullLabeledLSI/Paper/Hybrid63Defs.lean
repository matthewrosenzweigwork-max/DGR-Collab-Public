import FullLabeledLSI.Defs.F05_FiniteRank
import FullLabeledLSI.Defs.F06_Hybrid
import FullLabeledLSI.Defs.F02_Constants
import FullLabeledLSI.Paper.Lindeberg1

/-!
# Proposition 6.3: interface definitions (lane 3)

* `zext`, `Gcoll`: zero extension of a vector of `J` modes to `ℕ`-indexed modes, and the collective
  Gaussian variable `G_m = n^{-1/2} ∑_{i ∉ Bs} y_{i,m}` for an arbitrary set `Bs` of retained labels
  (`Glow c δ w m = Gcoll (retained c δ) w.2 m` by `rfl`).
* `PosIPlus A R σ`: `1 + T_R ≥ (σ/2)` on vectors supported on `s R` (the form delivered by
  `positivity_export`).
* `HybridInequality`: **interface** (manuscript (7.16)-(7.17), lane 4: `Paper/HybridGround`): the exact
  hybrid comparison inequality
  `0 ≤ ℰ̃(F̃) + ∫ F̃² v_R(G) - (b_R/2) [Ent(F̃²) + ∫ F̃² u_R(G) + log κ_R ∫ F̃²]`
  for `F̃ = polyB e c Bs` on the hybrid space.
* `RLSLeLamOne`: **interface**: `r_LS(μ) ≤ λ_1`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

/-- Zero extension of a vector of `J` modes to `ℕ`-indexed modes: index `m < J` is mode `m`
(stands for the manuscript's mode `m + 1`). -/
def zext {J : ℕ} (z : Fin J → ℝ) : ℕ → ℝ := fun n => if h : n < J then z ⟨n, h⟩ else 0

/-- `Gcoll Bs y m = n^{-1/2} ∑_{i ∉ Bs} y_{i,m}`, `n = N - |Bs|`. -/
def Gcoll {N J : ℕ} (Bs : Finset (Fin N)) (y : Fin N → Fin J → ℝ) (m : Fin J) : ℝ :=
  (Real.sqrt ((N - Bs.card : ℕ) : ℝ))⁻¹ * ∑ i ∈ Bsᶜ, y i m

theorem Glow_eq_Gcoll {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (w : Config N d × (Fin N → Fin J → ℝ)) :
    Glow c δ w = Gcoll (retained c δ) w.2 := rfl

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- `1 + T_R ≥ (σ/2)` on vectors supported on `s R` (the form of `positivity_export`). -/
def PosIPlus (A : FiniteRankApprox W μ e) (R : ℕ) (σ : ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ i, i ∉ A.s R → v i = 0) →
    ∑ i ∈ A.s R, ∑ j ∈ A.s R, v i * ((if i = j then 1 else 0) + A.a R i j) * v j ≥
      (σ / 2) * ∑ i ∈ A.s R, v i ^ 2

/-- **Interface (manuscript (7.16)-(7.17)).** The exact hybrid comparison inequality. -/
def HybridInequality {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ) (R : ℕ) : Prop :=
  ∀ σ : ℝ, 0 < σ → PosIPlus A R σ → IsInverseOfIPlus (A.a R) (CR R) →
    ∀ (J : ℕ), (∀ i ∈ A.s R, i < J) → ∀ (L : ℝ) (N : ℕ) (Bs : Finset (Fin N)), Bs.card < N →
      ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
        0 ≤ (∑ j, (∑ i, lam (j i)) * c j ^ 2)
          + ∫ w, polyB e c Bs w ^ 2 * vR A lam R (zext (Gcoll Bs w.2))
              ∂hybMeasure (μ : Measure (Torus d)) N J
          - (bRate (μ : Measure (Torus d)) lam (CR R)).toReal / 2 *
              ((ent (hybMeasure (μ : Measure (Torus d)) N J) (fun w => polyB e c Bs w ^ 2)).toReal
                + ∫ w, polyB e c Bs w ^ 2 * uR A R (zext (Gcoll Bs w.2))
                    ∂hybMeasure (μ : Measure (Torus d)) N J
                + Real.log (kappaR A R) *
                    ∫ w, polyB e c Bs w ^ 2 ∂hybMeasure (μ : Measure (Torus d)) N J)

/-- **Interface**: `r_LS(μ) ≤ λ_1` (to be proved in `Paper/HybridRLS`). -/
def RLSLeLamOne (μ : Measure (Torus d)) (lam : ℕ → ℝ) : Prop :=
  rLS μ ≤ ENNReal.ofReal (lam 1)

end SharpLSI.FL

end
