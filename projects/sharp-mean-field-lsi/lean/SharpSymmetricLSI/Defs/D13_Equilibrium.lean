import SharpSymmetricLSI.Defs.D06_Dissipation

/-!
# D13: equilibrium objects (2.1), (4.14), (4.15)

For the minimizer `μ` (a parameter here):
* `Top W μ h = T h = P_{μ,0}[W * (μ h)]`, `P_{μ,0} q = q - ∫ q dμ` (manuscript (2.1)),
  `(W*(μh))(x) = ∫ W(x,y) h(y) dμ(y)`.
* `secondVar W μ h = ⟨h, (I+T) h⟩_{L²(μ)}`, the quadratic form of `I + T`.
* `centeredKernel W μ = K`, `K(x,y) = W(x,y) - (W*μ)(x) - (W*μ)(y) + W(μ,μ)` (4.14),
  `J(ρ) = ½ K(ρ,ρ)`.
* `Ucentered W μ N = U_N = N J(L_N) = (1/(2N)) ∑_{i,j} K(xᵢ,xⱼ)` and
  `centeredPartition W μ N = K_N = ∫ e^{-U_N} dμ^{⊗N}` (4.15). `K_N` is distinct from `Z_N`.
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

/-- `h ∈ L²_0(μ)`. -/
def MemL20 (μ : Measure (Torus d)) (h : Torus d → ℝ) : Prop :=
  MemLp h 2 μ ∧ ∫ x, h x ∂μ = 0

/-- `T h = P_{μ,0}[W*(μh)]` (manuscript (2.1)). -/
noncomputable def Top (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (h : Torus d → ℝ)
    (x : Torus d) : ℝ :=
  (∫ y, W x y * h y ∂μ) - ∫ x', (∫ y, W x' y * h y ∂μ) ∂μ

/-- The quadratic form `⟨h, (I+T)h⟩_{L²(μ)}` of the second variation (manuscript (2.1)). -/
noncomputable def secondVar (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (h : Torus d → ℝ) : ℝ :=
  ∫ x, h x * (h x + Top W μ h x) ∂μ

/-- The centered kernel `K` (manuscript (4.14)). -/
noncomputable def centeredKernel (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (x y : Torus d) : ℝ :=
  W x y - convMeas W μ x - convMeas W μ y + interE W μ μ

/-- `J(ρ) = ½ K(ρ,ρ)` (manuscript (4.14)). -/
noncomputable def Jfun (W : Torus d → Torus d → ℝ) (μ ρ : Measure (Torus d)) : ℝ :=
  interE (centeredKernel W μ) ρ ρ / 2

/-- `U_N = N J(L_N) = (1/(2N)) ∑_{i,j} K(xᵢ,xⱼ)` (manuscript (4.15)). -/
noncomputable def Ucentered (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ)
    (X : Config N d) : ℝ :=
  1 / (2 * (N : ℝ)) * ∑ i, ∑ j, centeredKernel W μ (X i) (X j)

/-- The centered partition function `K_N = ∫ e^{-U_N} dμ^{⊗N}` (manuscript (4.15)). -/
noncomputable def centeredPartition (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (N : ℕ) : ℝ :=
  ∫ X, Real.exp (-Ucentered W μ N X) ∂Measure.pi (fun _ : Fin N => μ)

end SharpLSI
