import SharpSymmetricLSI.Infra.WeakGrad

/-!
# Classical derivatives on tori, Fourier coefficients, `H^2`

For a function `f` on `𝕋^ι` with smooth periodic lift, classical partial derivatives are taken
on the lift at the representative `repTorus y ∈ [0,1)^ι` (any representative gives the same
value by periodicity). Configuration-space versions go through `flat`/`unflat`.

`fourierCoeffT f k = ∫ f · conj(e_k) dm^{⊗ι}`, `e_k(y) = exp(2πi k·y)` (Mathlib's
`UnitAddTorus.mFourier`), w.r.t. the normalized Haar measure. `MemH2 f`:
`∑_k (1+|k|²)² |f̂(k)|² < ∞` (manuscript, proof of Proposition 3.5, Step 2).
-/

open MeasureTheory
open scoped ContDiff ComplexConjugate

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The representative of `y ∈ 𝕋^ι` in `[0,1)^ι`. -/
noncomputable def repTorus (y : UnitAddTorus ι) : ι → ℝ :=
  fun i => ((AddCircle.equivIco (1 : ℝ) 0 (y i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)

/-- Classical partial derivative `∂_k f (y)`. -/
noncomputable def cpartial (f : UnitAddTorus ι → ℝ) (k : ι) (y : UnitAddTorus ι) : ℝ :=
  fderiv ℝ (f ∘ liftT) (repTorus y) (Pi.single k 1)

/-- Classical second partial derivative `∂_l ∂_k f (y)`. -/
noncomputable def cpartial2 (f : UnitAddTorus ι → ℝ) (k l : ι) (y : UnitAddTorus ι) : ℝ :=
  fderiv ℝ (fun x => fderiv ℝ (f ∘ liftT) x (Pi.single k 1)) (repTorus y) (Pi.single l 1)

/-- Fourier coefficient `f̂(k) = ∫ f · conj(e_k) dm^{⊗ι}`. -/
noncomputable def fourierCoeffT (f : UnitAddTorus ι → ℝ) (k : ι → ℤ) : ℂ :=
  ∫ y, (f y : ℂ) * conj (UnitAddTorus.mFourier k y)

/-- `f ∈ H^2(𝕋^ι)` via Fourier coefficients. -/
def MemH2 (f : UnitAddTorus ι → ℝ) : Prop :=
  MemLp f 2 volume ∧
    Summable (fun k : ι → ℤ => (1 + ∑ i, ((k i : ℝ)) ^ 2) ^ 2 * ‖fourierCoeffT f k‖ ^ 2)

/-! ### Configuration spaces -/

variable {N d : ℕ}

/-- A function on `(𝕋^d)^N` is smooth if its periodic lift is `C^∞`. -/
def IsSmoothC (f : Config N d → ℝ) : Prop := IsSmoothT (f ∘ unflat)

/-- Classical partial derivative `∂_{i,k} f (X)` on `(𝕋^d)^N`. -/
noncomputable def cpartialC (f : Config N d → ℝ) (i : Fin N) (k : Fin d) (X : Config N d) : ℝ :=
  cpartial (f ∘ unflat) (i, k) (flat X)

/-- Classical second partial derivative `∂_{j,l} ∂_{i,k} f (X)` on `(𝕋^d)^N`. -/
noncomputable def cpartial2C (f : Config N d → ℝ) (i : Fin N) (k : Fin d) (j : Fin N)
    (l : Fin d) (X : Config N d) : ℝ :=
  cpartial2 (f ∘ unflat) (i, k) (j, l) (flat X)

/-- Laplacian `Δf = ∑_{i,k} ∂²_{i,k} f`. -/
noncomputable def laplacianC (f : Config N d → ℝ) (X : Config N d) : ℝ :=
  ∑ i, ∑ k, cpartial2C f i k i k X

/-- `∇f · ∇g = ∑_{i,k} ∂_{i,k} f ∂_{i,k} g` (classical). -/
noncomputable def gradDotC (f g : Config N d → ℝ) (X : Config N d) : ℝ :=
  ∑ i, ∑ k, cpartialC f i k X * cpartialC g i k X

/-- `H^2` on `(𝕋^d)^N`. -/
def MemH2C (f : Config N d → ℝ) : Prop := MemH2 (f ∘ unflat)

end SharpLSI
