import SharpSymmetricLSI.Defs.D15_Forces
import SharpSymmetricLSI.Infra.Classical

/-!
# F4: randomly revealing the original labels (5.6)–(5.8), (5.13)

For a probability `ν` on `(𝕋^d)^N`, a set `S` of revealed labels (`|S| = j`), its complement
`R = Sᶜ` (`n = N - j`):
* `restrictS S X = X_S`; `condLawS ν S i = ρ_{S,i} = ν(X_i ∈ · | X_S)` and
  `condJointS ν S I = ν_{S,I_1,…,I_k}`, the joint conditional law of `(X_{I_1}, …, X_{I_k})` given
  `X_S`, as Markov kernels from `X_S` (`condDistrib`, defined up to a.e. equality), (5.6), (5.8).
* `barCond ν S X = ρ̄_S = n⁻¹ ∑_{i ∈ R} ρ_{S,i}` evaluated at the revealed values `X_S` (5.6).
* `hRev ν μ j = h_j` (5.7) and `dRev ν j k = d_{j,k}` (5.8): the expectation includes the uniform
  choice of `S` among the `j`-subsets, the uniform choice of `i ∈ R` (resp. of an ordered tuple of
  `k` distinct labels in `R`), and integration of `X` under `ν`. Values in `ℝ≥0∞`; `hRev` is `0` for
  `j ≥ N` and `dRev` is `0` unless `j + k ≤ N`.
* `condForceS W μ ν S X x = B_S(x) = ∫ b(x,y) dρ̄_S(y)` (5.13), with `b = ∇₁K = bForce` (D15).
  `bForce` is a weak gradient, determined only a.e.; the value of `condForceS` is independent of
  the representative when `HasSmoothPosDensity ν` (then `ρ̄_S ≪ m`), which every statement assumes.
* `HasSmoothPosDensity ν`: `ν` has a smooth strictly positive density w.r.t. `m^{⊗N}`
  ("for now `ν` has a smooth positive density", start of Section 5.2).
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- `ν` has a smooth strictly positive density with respect to `m^{⊗N}`. -/
def HasSmoothPosDensity (ν : Measure (Config N d)) : Prop :=
  ∃ u : Config N d → ℝ, IsSmoothC u ∧ (∀ X, 0 < u X) ∧
    ν = (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (u X))

/-- The revealed coordinates `X_S`. -/
def restrictS (S : Finset (Fin N)) (X : Config N d) : S → Torus d := fun i => X i

/-- `ρ_{S,i} = ν(X_i ∈ · | X_S)` (manuscript (5.6)). -/
noncomputable def condLawS (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N))
    (i : Fin N) : Kernel (S → Torus d) (Torus d) :=
  condDistrib (fun X : Config N d => X i) (restrictS S) ν

/-- The joint conditional law of `(X_{I_1}, …, X_{I_k})` given `X_S` (manuscript (5.8)). -/
noncomputable def condJointS (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N))
    {k : ℕ} (I : Fin k → Fin N) : Kernel (S → Torus d) (Fin k → Torus d) :=
  condDistrib (fun X : Config N d => fun l => X (I l)) (restrictS S) ν

/-- `ρ̄_S = n⁻¹ ∑_{i ∈ R} ρ_{S,i}` at the revealed values of `X` (manuscript (5.6)). -/
noncomputable def barCond (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N))
    (X : Config N d) : Measure (Torus d) :=
  ((Sᶜ.card : ℝ≥0∞)⁻¹) • ∑ i ∈ Sᶜ, condLawS ν S i (restrictS S X)

/-- The ordered `k`-tuples of distinct labels in `R = Sᶜ`. -/
def distinctTuples (S : Finset (Fin N)) (k : ℕ) : Finset (Fin k → Fin N) :=
  Finset.univ.filter fun I => Function.Injective I ∧ ∀ l, I l ∉ S

/-- `h_j = E (1/n) ∑_{i ∈ R} H(ρ_{S,i} | μ)` (manuscript (5.7)), `0` for `j ≥ N`. -/
noncomputable def hRev (ν : Measure (Config N d)) [IsFiniteMeasure ν] (μ : Measure (Torus d))
    (j : ℕ) : ℝ≥0∞ :=
  if j < N then
    ((Nat.choose N j : ℝ≥0∞)⁻¹) * ∑ S ∈ Finset.univ.powersetCard j,
      ((Sᶜ.card : ℝ≥0∞)⁻¹) * ∑ i ∈ Sᶜ, ∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) μ ∂ν
  else 0

/-- `d_{j,k} = E H(ν_{S,I_1..I_k} | ρ_{S,I_1} ⊗ ⋯ ⊗ ρ_{S,I_k})` (manuscript (5.8)), with ordered
distinct `I_1, …, I_k ∈ R` uniform; `0` unless `j + k ≤ N`. -/
noncomputable def dRev (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j k : ℕ) : ℝ≥0∞ :=
  if j + k ≤ N then
    ((Nat.choose N j : ℝ≥0∞)⁻¹) * ∑ S ∈ Finset.univ.powersetCard j,
      ((Nat.descFactorial (N - j) k : ℝ≥0∞)⁻¹) * ∑ I ∈ distinctTuples S k,
        ∫⁻ X, klDiv (condJointS ν S I (restrictS S X))
          (Measure.pi fun l => condLawS ν S (I l) (restrictS S X)) ∂ν
  else 0

/-- `B_S(x) = ∫ b(x,y) dρ̄_S(y)` (manuscript (5.13)), component `k`. -/
noncomputable def condForceS (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (ν : Measure (Config N d)) [IsFiniteMeasure ν] (S : Finset (Fin N)) (X : Config N d)
    (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, bForce W μ x y k ∂barCond ν S X

end SharpLSI.FL
