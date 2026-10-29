import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CosineCalculus
import SharpSymmetricLSI.Paper.CosineGenerator
import SharpSymmetricLSI.Paper.CosineSecondOrder

/-!
# R41: Lemma 3.7 (`lem:cosine-second-order`), second-order inequality

Manuscript (3.33)–(3.36) and Lemma 3.7, (3.34). `L_N g = Δg - ∇U_N·∇g` (`cosGen`).
* (3.33) `∫ (L_N g) w dP_{N,κ} = -∫ ∇g·∇w dP_{N,κ}` for smooth `g`, `w`.
* (3.35) `∂_j∂_k U_N = (aκ/N) cos(2π(x_j - x_k))` for `j ≠ k`,
  `∂_j² U_N = -(aκ/N) Re(e^{2πix_j} conj(b_j))`, `b_j = S - e^{2πix_j}`, `S = ∑ e^{2πix_l}`.
* (3.36) `∑_{j≠k} ∂_j∂_k U_N v_j v_k ≥ -(aκ/N) |v|²`.
* (3.34) `∫ (L_N g)² dP_{N,κ} ≥ a(e^{-2κ} - κ/N) ∫ |∇g|² dP_{N,κ}` for every smooth `g`.
Derivatives are classical (smooth functions); the coordinate of particle `j` is `(j, 0)`.
-/

open MeasureTheory

namespace SharpLSI

/-- (3.33): integration by parts for `L_N`. -/
theorem cosine_generator_ibp (κ : ℝ) {N : ℕ} (hN : 1 ≤ N) {g w : Config N 1 → ℝ}
    (hg : IsSmoothC g) (hw : IsSmoothC w) :
    ∫ X, cosGen κ N g X * w X ∂gibbs cosV (cosW κ) N =
      -∫ X, gradDotC g w X ∂gibbs cosV (cosW κ) N := by
  exact cosine_generator_ibp_aux κ hg hw

/-- (3.35): the Hessian of `U_N`. -/
theorem cosine_hessian (κ : ℝ) {N : ℕ} (hN : 1 ≤ N) (X : Config N 1) :
    (∀ j k : Fin N, j ≠ k →
      cpartial2C (cosU κ N) j 0 k 0 X = aCos * κ / N * gCos (X j - X k)) ∧
    ∀ j : Fin N, cpartial2C (cosU κ N) j 0 j 0 X =
      -(aCos * κ / N) * (expT (X j) * (starRingEnd ℂ) ((∑ l, expT (X l)) - expT (X j))).re := by
  exact cosine_hessian_aux κ X

/-- (3.36): the off-diagonal part of the Hessian of `U_N` is `≥ -(aκ/N) I`. -/
theorem cosine_offdiagonal (κ : ℝ) (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (X : Config N 1)
    (v : Fin N → ℝ) :
    -(aCos * κ / N) * ∑ j, v j ^ 2 ≤
      ∑ j, ∑ k, (if j ≠ k then cpartial2C (cosU κ N) j 0 k 0 X * v j * v k else 0) := by
  exact cosine_offdiagonal_aux κ hκ X v

/-- Lemma 3.7, (3.34). -/
theorem cosine_second_order {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) {g : Config N 1 → ℝ}
    (hg : IsSmoothC g) :
    aCos * (Real.exp (-2 * κ) - κ / N) * ∫ X, gradDotC g g X ∂gibbs cosV (cosW κ) N ≤
      ∫ X, cosGen κ N g X ^ 2 ∂gibbs cosV (cosW κ) N := by
  exact cosine_second_order_aux hκ hg

end SharpLSI
