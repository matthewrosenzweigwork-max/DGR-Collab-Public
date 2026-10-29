import Mathlib

/-!
# Lane D, Task B: sequence-level quantities of the Fourier concavity estimate (Lemma 9.11)

Pure definitions on real sequences `ℕ → ℝ` (index `j ≥ 1` is the frequency `4πj`; weights carry a
factor `j k`, so the index-`0` terms vanish).  `r = 1/100`.

* `Ncos x = ∑_j j² r^j x_j²`  (so that `Q_C(σ) = 512π² (Ncos c + Ncos d)`);
* `Tcos`, `Tsin`: the cross terms of the Hessian at a Dirac mass, in the cosine and sine sectors
  (`x_0 = 0` encodes that `σ` has mass zero).
-/

open scoped BigOperators

namespace SharpLSI.FL.Ex.LaneD

/-- The weight `j k r^{j+k}`, `r = 1/100`. -/
noncomputable def wgt (p : ℕ × ℕ) : ℝ := (p.1 : ℝ) * p.2 * (1 / 100 : ℝ) ^ (p.1 + p.2)

/-- `∑_j j² r^j x_j²`. -/
noncomputable def Ncos (x : ℕ → ℝ) : ℝ := ∑' j : ℕ, (j : ℝ) ^ 2 * (1 / 100 : ℝ) ^ j * x j ^ 2

/-- Cosine sector: `∑_{j,k} j k r^{j+k} x_j (x_{|k-j|} - x_{k+j})`. -/
noncomputable def Tcos (x : ℕ → ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, wgt p * x p.1 * (x (Nat.dist p.1 p.2) - x (p.1 + p.2))

/-- `sgn(k - j)` as a real number. -/
noncomputable def sgnk (j k : ℕ) : ℝ := if j < k then 1 else if k < j then -1 else 0

/-- Sine sector: `(∑_j j r^j y_j)² - ∑_{j,k} j k r^{j+k} y_j (y_{k+j} + sgn(k-j) y_{|k-j|})`. -/
noncomputable def Tsin (y : ℕ → ℝ) : ℝ :=
  (∑' j : ℕ, (j : ℝ) * (1 / 100 : ℝ) ^ j * y j) ^ 2 -
    ∑' p : ℕ × ℕ, wgt p * y p.1 * (y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2))

end SharpLSI.FL.Ex.LaneD
