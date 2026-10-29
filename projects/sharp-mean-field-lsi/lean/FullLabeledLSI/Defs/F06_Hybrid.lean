import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# F6: tensor coefficients, influences and the hybrid space (7.1)–(7.10)

Data of Section 7. `μ` is a probability on `𝕋^d`, `(e, lam)` a reference eigenbasis in the
manuscript's indexing (`e 0 = 1`, `lam 0 = 0`, D16), and `J` the number of feature modes.
* A coefficient array `c : (Fin N → Fin (J+1)) → ℝ` assigns `c_j` to the multi-index `j`, with
  `j_i ∈ {0, …, J}`; `polyEval e c X = ∑_j c_j ∏ᵢ e_{jᵢ}(Xᵢ)` is the polynomial (7.1) (the factor
  with `jᵢ = 0` is `e_0 = 1`). `SpectralCoeff lam L c`: `c_j ≠ 0 → ∑ᵢ λ_{jᵢ} ≤ L` (7.1).
* `infl c i = ∑_{j : jᵢ ≠ 0} c_j²` is the influence (7.4) (its coefficient form; the variance
  form is a lemma). `retained c δ = B_N = {i : Inf_i > δ}` (7.6).
* The hybrid space (7.7) is realized on `Config N d × (Fin N → Fin J → ℝ)` with the product of
  `μ^{⊗N}` and `γ_J^{⊗N}`; on retained labels only the torus coordinate is read and on the other
  labels only the Gaussian coordinate is read, so integrals of such functions are integrals
  against `μ^{⊗B_N} ⊗ γ_J^{⊗B_N^c}`. `hybEval` is `F̃_N`: the same polynomial with
  `e_m(Xᵢ)` replaced by `y_{i,m}` (`m ≥ 1`) on labels outside `B_N`.
* `lowCount = n = N - |B_N|`; `Zlow` (7.10) and `Glow` (its Gaussian replacement) are indexed by
  `m : Fin J`, standing for the manuscript's mode `m + 1`.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The polynomial (7.1) with coefficient array `c`. -/
noncomputable def polyEval (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (X : Config N d) : ℝ :=
  ∑ j, c j * ∏ i, e (j i) (X i)

/-- The coefficients are supported on multi-indices with `∑ᵢ λ_{jᵢ} ≤ L` (7.1). -/
def SpectralCoeff (lam : ℕ → ℝ) (L : ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) : Prop :=
  ∀ j, c j ≠ 0 → ∑ i, lam (j i) ≤ L

/-- The influence `Inf_i = ∑_{j : jᵢ ≠ 0} c_j²` (7.4). -/
noncomputable def infl {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin N → Fin (J + 1) => j i ≠ 0), c j ^ 2

/-- The retained labels `B_N = {i : Inf_i > δ}` (7.6). -/
noncomputable def retained {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => δ < infl c i)

/-- `n = N - |B_N|`, the number of replaced labels. -/
noncomputable def lowCount {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℕ :=
  N - (retained c δ).card

/-- The hybrid reference probability (7.7), realized on `Config N d × (Fin N → Fin J → ℝ)`. -/
noncomputable def hybMeasure (μ : Measure (Torus d)) (N J : ℕ) :
    Measure (Config N d × (Fin N → Fin J → ℝ)) :=
  (Measure.pi fun _ : Fin N => μ).prod
    (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1)

/-- One factor of `F̃_N`: `e_m(Xᵢ)` on retained labels; `1` for `m = 0` and `y_{i,m}` for `m ≥ 1`
on replaced labels. -/
noncomputable def hybFactor (e : ℕ → Torus d → ℝ) {N J : ℕ} (B : Finset (Fin N)) (i : Fin N)
    (m : Fin (J + 1)) (ω : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  if i ∈ B then e m (ω.1 i)
  else if h : (m : ℕ) = 0 then 1 else ω.2 i ⟨(m : ℕ) - 1, by omega⟩

/-- `F̃_N`, the polynomial (7.1) evaluated on the hybrid space (Section 7.1). -/
noncomputable def hybEval (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (δ : ℝ) (ω : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  ∑ j, c j * ∏ i, hybFactor e (retained c δ) i (j i) ω

/-- `Z^low_{N,m+1} = n^{-1/2} ∑_{i ∉ B_N} e_{m+1}(Xᵢ)` (7.10). -/
noncomputable def Zlow (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (δ : ℝ) (X : Config N d) (m : Fin J) : ℝ :=
  (Real.sqrt (lowCount c δ))⁻¹ * ∑ i ∈ (retained c δ)ᶜ, e ((m : ℕ) + 1) (X i)

/-- `G_{N,m+1} = n^{-1/2} ∑_{i ∉ B_N} y_{i,m+1}`, the replacement of `Z^low` (Section 7.3). -/
noncomputable def Glow {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (ω : Config N d × (Fin N → Fin J → ℝ)) (m : Fin J) : ℝ :=
  (Real.sqrt (lowCount c δ))⁻¹ * ∑ i ∈ (retained c δ)ᶜ, ω.2 i m

end SharpLSI.FL
