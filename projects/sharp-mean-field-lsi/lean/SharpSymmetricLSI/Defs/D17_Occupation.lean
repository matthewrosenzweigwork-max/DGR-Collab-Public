import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# D17: occupation basis (7.1) and Hermite basis (7.2)

Occupation vectors `α = (α_j)_{j≥1}` are finitely supported; Lean `α : ℕ →₀ ℕ` with `α n`
the manuscript's `α_{n+1}` (same index shift as D16).
* `occBasis e α N = B_{α,N}` (7.1): with `q = |α| ≤ N`,
  `B_{α,N} = √(α!/(N)_q) ∑_{(I_j) pairwise disjoint, |I_j| = α_j} ∏_j ∏_{i∈I_j} e_j(X_i)`.
  A family `(I_j)` is encoded as a labelling `c : Fin N → ℕ` (`c i = n+1` iff `i ∈ I_{n+1}`,
  `c i = 0` iff `i` carries `e_0 = 1`) with `#{i | c i = n+1} = α n`. For `q > N` the sum is
  empty and `B_{α,N} = 0` ("padded by zeros").
* `hermiteBasis α = h_α`, `h_α(z) = ∏_j He_{α_j}(z_j)/√(α_j!)` (7.2), `He` = Mathlib's
  (probabilists') `Polynomial.hermite`.
* `occEnergy lam α = Λ_α = ∑_j λ_j α_j`.
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

/-- `|α| = ∑_j α_j`. -/
def occSize (α : ℕ →₀ ℕ) : ℕ := α.sum fun _ k => k

/-- `α! = ∏_j α_j!`. -/
def occFactorial (α : ℕ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

/-- `Λ_α = ∑_j λ_j α_j` (Lean `λ_{n+1} α n`). -/
noncomputable def occEnergy (lam : ℕ → ℝ) (α : ℕ →₀ ℕ) : ℝ :=
  α.sum fun n k => lam (n + 1) * k

/-- The labellings `c : Fin N → ℕ` encoding the disjoint families `(I_j)` of (7.1). -/
noncomputable def occLabellings (α : ℕ →₀ ℕ) (N : ℕ) : Finset (Fin N → Fin (α.support.sup id + 2)) :=
  by classical exact Finset.univ.filter fun c =>
    ∀ n : ℕ, (Finset.univ.filter fun i => (c i : ℕ) = n + 1).card = α n

/-- The occupation basis function `B_{α,N}` (manuscript (7.1)). -/
noncomputable def occBasis (e : ℕ → Torus d → ℝ) (α : ℕ →₀ ℕ) (N : ℕ) (X : Config N d) : ℝ :=
  Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) *
    ∑ c ∈ occLabellings α N, ∏ i, e (c i : ℕ) (X i)

/-- The Hermite basis function `h_α` (manuscript (7.2)). -/
noncomputable def hermiteBasis (α : ℕ →₀ ℕ) (z : ℕ → ℝ) : ℝ :=
  ∏ n ∈ α.support, Polynomial.aeval (z n) (Polynomial.hermite (α n)) /
    Real.sqrt ((α n).factorial : ℝ)

end SharpLSI
