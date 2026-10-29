import SharpSymmetricLSI.Defs.D13_Equilibrium

/-!
# D14: conditional laws and conditional entropies (5.1), (5.2)

For a probability `ν` on `(𝕋^d)^N` and `0 ≤ j`, `j + k ≤ N`:
* `past j X = (X_1, …, X_j)`, `block j k X = (X_{j+1}, …, X_{j+k})` (Lean indices `0, …`).
* `condNext ν j = ρ_j = ν(X_{j+1} ∈ · | ℱ_j)` and `condBlock ν j k = ν_{j,k}` (5.1), as Markov
  kernels from the past (`ProbabilityTheory.condDistrib`; defined up to a.e. equality).
* `hCond ν μ j = h_j = E_ν H(ρ_j | μ)` and `DCond ν j k = D_{j,k} = E_ν H(ν_{j,k} | ρ_j^{⊗k})`
  (5.2), in `ℝ≥0∞`.
* `IsSymmetricMeasure ν`: invariance under all coordinate permutations.
* Empirical measure `L_N` and `B(L_N^{⊗k}) = N^{-k} ∑_{i_1..i_k} B(X_{i_1}, …, X_{i_k})`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

/-- `ν` is invariant under permutations of the particles. -/
def IsSymmetricMeasure (ν : Measure (Config N d)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ν.map (fun X => X ∘ σ) = ν

/-- The past `(X_1, …, X_j)`. -/
def past (j : ℕ) (hj : j ≤ N) (X : Config N d) : Fin j → Torus d :=
  fun i => X (Fin.castLE hj i)

/-- The block `(X_{j+1}, …, X_{j+k})`. -/
def block (j k : ℕ) (h : j + k ≤ N) (X : Config N d) : Fin k → Torus d :=
  fun a => X ⟨j + a, by omega⟩

/-- `ρ_j = ν(X_{j+1} ∈ · | ℱ_j)` (manuscript (5.1)). -/
noncomputable def condNext (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j : ℕ)
    (hj : j < N) : ProbabilityTheory.Kernel (Fin j → Torus d) (Torus d) :=
  condDistrib (fun X : Config N d => X ⟨j, hj⟩) (past j hj.le) ν

/-- `ν_{j,k} = ν((X_{j+1}, …, X_{j+k}) ∈ · | ℱ_j)` (manuscript (5.1)). -/
noncomputable def condBlock (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j k : ℕ)
    (h : j + k ≤ N) : ProbabilityTheory.Kernel (Fin j → Torus d) (Fin k → Torus d) :=
  condDistrib (block j k h) (past j (by omega)) ν

/-- `h_j = E_ν H(ρ_j | μ)` (manuscript (5.2)). -/
noncomputable def hCond (ν : Measure (Config N d)) [IsFiniteMeasure ν] (μ : Measure (Torus d))
    (j : ℕ) (hj : j < N) : ℝ≥0∞ :=
  ∫⁻ X, klDiv (condNext ν j hj (past j hj.le X)) μ ∂ν

/-- `D_{j,k} = E_ν H(ν_{j,k} | ρ_j^{⊗k})` (manuscript (5.2)); requires `j < N` for `ρ_j`. -/
noncomputable def DCond (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j k : ℕ)
    (hj : j < N) (h : j + k ≤ N) : ℝ≥0∞ :=
  ∫⁻ X, klDiv (condBlock ν j k h (past j hj.le X))
    (Measure.pi (fun _ : Fin k => condNext ν j hj (past j hj.le X))) ∂ν

/-- `h_j` as a total function of `j` (`0` for `j ≥ N`), for sums over ranges. -/
noncomputable def hCondT (ν : Measure (Config N d)) [IsFiniteMeasure ν] (μ : Measure (Torus d))
    (j : ℕ) : ENNReal :=
  if h : j < N then hCond ν μ j h else 0

/-- `D_{j,k}` as a total function (`0` unless `j < N` and `j + k ≤ N`). -/
noncomputable def DCondT (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j k : ℕ) : ENNReal :=
  if h : j < N ∧ j + k ≤ N then DCond ν j k h.1 h.2 else 0

/-- `E_ν B(ρ_j^{⊗k}) = ∫ (∫ B d ρ_j(past)^{⊗k}) dν` (total in `j`, `0` for `j ≥ N`). -/
noncomputable def condProductMean (ν : Measure (Config N d)) [IsFiniteMeasure ν] (k : ℕ)
    (B : (Fin k → Torus d) → ℝ) (j : ℕ) : ℝ :=
  if h : j < N then
    ∫ X, (∫ z, B z ∂Measure.pi (fun _ : Fin k => condNext ν j h (past j h.le X))) ∂ν
  else 0

/-- `B(η) = ∫ B dη` evaluated at `L_N^{⊗k}`: `N^{-k} ∑_{i : Fin k → Fin N} B(X ∘ i)`. -/
noncomputable def empiricalTensor (k : ℕ) (B : (Fin k → Torus d) → ℝ) (X : Config N d) : ℝ :=
  (N : ℝ)⁻¹ ^ k * ∑ i : Fin k → Fin N, B (X ∘ i)

end SharpLSI
