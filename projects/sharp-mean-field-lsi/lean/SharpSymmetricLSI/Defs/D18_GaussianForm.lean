import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# D18: the limiting Dirichlet form and the Gaussian constant (8.1), (8.9)

* `Cyl`: compactly supported smooth cylindrical functions `z ↦ φ(z_1, …, z_J)`,
  `φ ∈ C_c^∞(ℝ^J)` (Lean coordinates `z 0, …, z (J-1)`).
* `Cyl.form lam' γ φ = ∫ ∑_j λ_j |∂_j φ|² dγ` (manuscript (8.1)).
* `gaussForm lam' γ = ℰ_∞`: the closure of (8.1), encoded as its lower-semicontinuous
  relaxation in `L²(γ)`: `ℰ_∞(f) = inf { liminf ℰ(φ_n) : φ_n cylindrical, φ_n → f in L²(γ) }`.
  For a closable form (proved in Section 8.1, R32) the relaxation is the closure (B. Simon,
  "A canonical decomposition for quadratic forms", 1978). REVIEW.
* `lamG lam' C = λ_G = inf_{v ∈ D(Λ^{1/2}) \ 0} ⟨v,Λv⟩/⟨v,Cv⟩` (manuscript (8.9)).
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

/-- A compactly supported smooth cylindrical function on `ℝ^ℕ`. -/
structure Cyl where
  J : ℕ
  φ : (Fin J → ℝ) → ℝ
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

namespace Cyl

/-- Evaluation `z ↦ φ(z_0, …, z_{J-1})`. -/
def eval (c : Cyl) (z : ℕ → ℝ) : ℝ := c.φ (fun i => z i)

/-- The pre-closure Gaussian form (manuscript (8.1)) on a cylindrical function. -/
noncomputable def form (lam' : ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (c : Cyl) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal
    (∑ i : Fin c.J, lam' i * (fderiv ℝ c.φ (fun j => z j) (Pi.single i 1)) ^ 2) ∂γ

end Cyl

/-- `ℰ_∞`, the closure of (8.1) in `L²(γ)`, as its lower-semicontinuous relaxation. -/
noncomputable def gaussForm (lam' : ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (f : (ℕ → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨅ (u : ℕ → Cyl) (_ : Tendsto (fun n => eLpNorm (fun z => (u n).eval z - f z) 2 γ) atTop
      (𝓝 0)),
    liminf (fun n => (u n).form lam' γ) atTop

/-- `λ_G` (manuscript (8.9)): infimum of `⟨v,Λv⟩/⟨v,Cv⟩` over nonzero `v ∈ ℓ²` with
`∑ λ_j v_j² < ∞`. -/
noncomputable def lamG (lam' : ℕ → ℝ) (C : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨅ v ∈ {v : ℕ → ℝ | Summable (fun i => v i ^ 2) ∧ Summable (fun i => lam' i * v i ^ 2) ∧
      v ≠ 0},
    ENNReal.ofReal (∑' i, lam' i * v i ^ 2) / ENNReal.ofReal (∑' i, v i * ∑' j, C i j * v j)

/-- The Gaussian generator (manuscript (8.2)) on a cylindrical function, given the Gaussian
row variables `Y i ≈ (Tz)_i` (each the `L²(γ_∞)` limit of `∑_{q<n} T_{iq} z_q`, see
`IsRowVariable`): `L_∞φ = ∑_i λ_i [∂_{ii}φ - (z_i + (Tz)_i) ∂_iφ]` (Lean indices shifted). -/
noncomputable def Cyl.gen (lam' : ℕ → ℝ) (Y : ℕ → (ℕ → ℝ) → ℝ) (c : Cyl) (z : ℕ → ℝ) : ℝ :=
  ∑ i : Fin c.J, lam' i *
    (fderiv ℝ (fun x => fderiv ℝ c.φ x (Pi.single i 1)) (fun j => z j) (Pi.single i 1) -
      (z i + Y i z) * fderiv ℝ c.φ (fun j => z j) (Pi.single i 1))

/-- `Y` is the `L²(γ)` row variable `(Tz)_i = ∑_q T_{iq} z_q`. -/
def IsRowVariable (T : ℕ → ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (i : ℕ) (Y : (ℕ → ℝ) → ℝ) : Prop :=
  MemLp Y 2 γ ∧ Tendsto (fun n => eLpNorm (fun z => (∑ q ∈ Finset.range n, T i q * z q) - Y z) 2 γ)
    atTop (𝓝 0)

end SharpLSI
