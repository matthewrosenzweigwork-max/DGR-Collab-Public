import SharpSymmetricLSI.Defs.D13_Equilibrium

/-!
# D16: reference spectrum and the Gaussian fluctuation law (6.1), (6.2), (6.10), (6.11)

* `IsRefEigenbasis μ e lam`: `(e_j)_{j ≥ 0}` is a real orthonormal basis of `L²(μ)` of
  eigenfunctions of `-L_μ`, `L_μ = Δ + ∇log μ·∇` defined by its symmetric form
  `∫ ∇f·∇g dμ` (weak eigen-equation in `H^1(μ)`), with `e_0 = 1` and nondecreasing eigenvalues
  (manuscript (6.1)). The basis is not unique; all statements quantify over every such basis.
* Indexing: the manuscript's coordinates `z_j`, `j ≥ 1`, are `z (j-1)` here, i.e. Lean index
  `n` corresponds to the manuscript's `n+1`. `lamShift lam n = λ_{n+1}`.
* `Tmat W μ e i j = T_{i+1,j+1} = ∬ K(x,y) e_{i+1}(x) e_{j+1}(y) dμ dμ` (6.2).
* `IsInverseOfIPlus T C`: `C = (I+T)^{-1}` (6.11), encoded by: every column of `C` is in `ℓ²`
  and `(I+T) C = I` entrywise (absolutely convergent row sums). Since `I+T ≥ σI` (Prop. 2.1)
  this determines `C` uniquely. REVIEW.
* `IsCenteredGaussianCov γ C`: `γ` is a probability on `ℝ^ℕ` all of whose finite linear
  functionals `∑_{i∈s} vᵢ zᵢ` are centered Gaussian with variance `∑_{i,j∈s} vᵢ C_{ij} vⱼ`
  (manuscript: "centered Gaussian with covariance operator `C`"; the continuous linear
  functionals on `ℝ^ℕ` are exactly the finitely supported ones).
-/

open MeasureTheory ProbabilityTheory

namespace SharpLSI

variable {d : ℕ}

/-- `(e, lam)` is a reference eigenbasis of `-L_μ` in `L²(μ)` (manuscript (6.1)). -/
structure IsRefEigenbasis (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) :
    Prop where
  zero : e 0 = fun _ => 1
  memH1 : ∀ j, MemH1 μ (e j)
  orthonormal : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0
  complete : ∀ f : Torus d → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0
  eigen : ∀ j (φ : Torus d → ℝ), MemH1 μ φ →
    ∫ x, ∑ k, weakGrad (e j) x k * weakGrad φ x k ∂μ = lam j * ∫ x, e j x * φ x ∂μ
  mono : Monotone lam

/-- `λ_{n+1}` (shift to the manuscript's indexing `j ≥ 1`). -/
def lamShift (lam : ℕ → ℝ) (n : ℕ) : ℝ := lam (n + 1)

/-- The matrix `T_{i+1,j+1}` of `T` in the reference basis (manuscript (6.2)). -/
noncomputable def Tmat (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (e : ℕ → Torus d → ℝ) (i j : ℕ) : ℝ :=
  ∫ x, ∫ y, centeredKernel W μ x y * e (i + 1) x * e (j + 1) y ∂μ ∂μ

/-- `C = (I+T)^{-1}` as an infinite matrix (manuscript (6.11)). -/
def IsInverseOfIPlus (T C : ℕ → ℕ → ℝ) : Prop :=
  ∀ j, Summable (fun k => C k j ^ 2) ∧
    ∀ i, Summable (fun k => |((if i = k then 1 else 0) + T i k) * C k j|) ∧
      ∑' k, ((if i = k then 1 else 0) + T i k) * C k j = if i = j then 1 else 0

/-- `γ` is a centered Gaussian probability on `ℝ^ℕ` with covariance `C`. -/
def IsCenteredGaussianCov (γ : Measure (ℕ → ℝ)) (C : ℕ → ℕ → ℝ) : Prop :=
  IsProbabilityMeasure γ ∧ ∀ (s : Finset ℕ) (v : ℕ → ℝ),
    γ.map (fun z => ∑ i ∈ s, v i * z i) =
      gaussianReal 0 (∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j).toNNReal

/-! ### Fluctuations, the reference Gaussian, the quadratic limit (6.5), (6.8)–(6.10) -/

/-- `Z_{N,n+1} = N^{-1/2} ∑_l e_{n+1}(X_l)` (manuscript (6.5); Lean index `n` ↔ `j = n+1`). -/
noncomputable def fluct (e : ℕ → Torus d → ℝ) (N : ℕ) (n : ℕ) (X : Config N d) : ℝ :=
  (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e (n + 1) (X l)

/-- The product standard Gaussian `γ` on `ℝ^ℕ` (manuscript, after (6.5)). -/
noncomputable def gammaRef : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- `Q` is the centered second Gaussian chaos `Q_T` of the Hilbert–Schmidt matrix `T` under `γ`
(manuscript (6.8)): the `L²(γ)` limit of `∑_{i,j<n} T_{ij}(z_i z_j - δ_{ij})`. This is the
coordinate-truncation characterization; it is independent of the orthonormal representation. -/
def IsSecondChaos (T : ℕ → ℕ → ℝ) (Q : (ℕ → ℝ) → ℝ) : Prop :=
  MemLp Q 2 gammaRef ∧
  Filter.Tendsto (fun n => eLpNorm (fun z => (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      T i j * (z i * z j - if i = j then 1 else 0)) - Q z) 2 gammaRef) Filter.atTop (nhds 0)

/-- `d_K = ∫ K(x,x) dμ(x)` (manuscript (6.9)). -/
noncomputable def diagMean (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) : ℝ :=
  ∫ x, centeredKernel W μ x x ∂μ

/-- `U_∞ = ½ Q_T + ½ d_K` (manuscript (6.9)). -/
noncomputable def Uinf (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (Q : (ℕ → ℝ) → ℝ) (z : ℕ → ℝ) : ℝ :=
  Q z / 2 + diagMean W μ / 2

/-- `K_∞ = ∫ e^{-U_∞} dγ` (manuscript (6.10)). -/
noncomputable def Kinf (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (Q : (ℕ → ℝ) → ℝ) : ℝ :=
  ∫ z, Real.exp (-Uinf W μ Q z) ∂gammaRef

/-- `γ_∞ = p_∞ γ`, `p_∞ = K_∞^{-1} e^{-U_∞}` (manuscript (6.10)). -/
noncomputable def gammaInfOf (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (Q : (ℕ → ℝ) → ℝ) : Measure (ℕ → ℝ) :=
  gammaRef.withDensity (fun z => ENNReal.ofReal (Real.exp (-Uinf W μ Q z) / Kinf W μ Q))

end SharpLSI
