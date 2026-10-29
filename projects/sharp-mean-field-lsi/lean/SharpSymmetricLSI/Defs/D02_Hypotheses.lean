import SharpSymmetricLSI.Infra.Torus

/-!
# D2: the standing hypotheses (1.2)

Manuscript (1.2): `V : 𝕋^d → ℝ`, `W : 𝕋^d × 𝕋^d → ℝ` finite-valued, there exist `K_V, K_W ≥ 0`
with `D²V ≥ -K_V I_d`, `D²W ≥ -K_W I_{2d}` as distributional inequalities on the whole torus,
`W(x,y) = W(y,x)`, `W(x,x) = 0`, the last two for the (bounded) Lipschitz representatives.

Encoding (owner decision 2026-10-03): the distributional Hessian bounds are tested on the
periodic lift against smooth, compactly supported, nonnegative `φ` and every direction `ξ`
(Euclidean norm). `V`, `W` are taken continuous: the symmetry/diagonal conditions concern the
Lipschitz representatives, which are the unique continuous ones; the existence of that
representative from the a.e. hypothesis is Appendix A.1 (R35). REVIEW.
-/

open MeasureTheory
open scoped ContDiff

namespace SharpLSI

/-- The second directional derivative `∂_ξ ∂_ξ φ (x)`. -/
noncomputable def secondDirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (ξ : E) (x : E) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ φ y ξ) x ξ

/-- Hypotheses (1.2) with constants `K_V`, `K_W`. -/
structure Hyp {d : ℕ} (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (KV KW : ℝ) : Prop where
  KV_nonneg : 0 ≤ KV
  KW_nonneg : 0 ≤ KW
  continuous_V : Continuous V
  continuous_W : Continuous (Function.uncurry W)
  /-- `D²V ≥ -K_V I_d` in the sense of distributions on the whole torus. -/
  semiconvex_V : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ x, 0 ≤ φ x) → ∀ ξ : Fin d → ℝ,
      -KV * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, V (liftT x) * secondDirDeriv φ ξ x
  /-- `D²W ≥ -K_W I_{2d}` in the sense of distributions on the whole torus `𝕋^d × 𝕋^d`. -/
  semiconvex_W : ∀ φ : (Fin d → ℝ) × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ p, 0 ≤ φ p) → ∀ ξ : (Fin d → ℝ) × (Fin d → ℝ),
      -KW * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) * ∫ p, φ p ≤
        ∫ p, W (liftT p.1) (liftT p.2) * secondDirDeriv φ ξ p
  symm : ∀ x y, W x y = W y x
  diag : ∀ x, W x x = 0

end SharpLSI
