import SharpSymmetricLSI.Infra.Torus
import SharpSymmetricLSI.Infra.TorusLift

/-!
# Weak gradients and `H^1` on tori

Weak gradients on a torus are defined through the periodic lift: `g` is a weak gradient of `f`
if `f ∘ liftT` and `g_k ∘ liftT` are locally integrable on `ℝ^ι` and, for every smooth compactly
supported `φ` on `ℝ^ι` and every coordinate `k`,
`∫ f(πx) ∂_k φ(x) dx = -∫ g_k(πx) φ(x) dx`.

`MemH1 P f`: `f` has a weak gradient, `f ∈ L²(P)` and `|∇f| ∈ L²(P)` (Euclidean norm). For the
measures in the manuscript (densities bounded above and below w.r.t. Haar measure) this is the
weighted Sobolev space `H^1(P)`.

`weakGrad f` is a chosen weak gradient (junk `0` if none exists); weak gradients are unique
almost everywhere (`weakGrad_ae_unique`), so all integrals against measures absolutely
continuous w.r.t. Haar measure are independent of the choice.
-/

open MeasureTheory
open scoped ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `g` is a weak gradient of `f` on the torus `𝕋^ι` (tested on the periodic lift). -/
structure IsWeakGrad (f : UnitAddTorus ι → ℝ) (g : UnitAddTorus ι → ι → ℝ) : Prop where
  locInt : LocallyIntegrable (f ∘ liftT)
  locInt_grad : ∀ k, LocallyIntegrable (fun x => g (liftT x) k)
  ibp : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ k : ι,
    ∫ x, f (liftT x) * fderiv ℝ φ x (Pi.single k 1) = -∫ x, g (liftT x) k * φ x

/-- `f` has a weak gradient. -/
def HasWeakGrad (f : UnitAddTorus ι → ℝ) : Prop := ∃ g, IsWeakGrad f g

open Classical in
/-- A chosen weak gradient (`0` if none exists). -/
noncomputable def weakGrad (f : UnitAddTorus ι → ℝ) : UnitAddTorus ι → ι → ℝ :=
  if h : HasWeakGrad f then h.choose else 0

/-- Squared Euclidean norm `|v|² = ∑ₖ vₖ²`. -/
def sqNorm (v : ι → ℝ) : ℝ := ∑ k, v k ^ 2

/-- Weak gradients are unique almost everywhere (w.r.t. Haar measure). -/
theorem weakGrad_ae_unique {f : UnitAddTorus ι → ℝ} {g g' : UnitAddTorus ι → ι → ℝ}
    (hg : IsWeakGrad f g) (hg' : IsWeakGrad f g') : g =ᵐ[volume] g' := by
  have hk : ∀ k, (fun x => g (liftT x) k) =ᵐ[(volume : Measure (ι → ℝ))]
      fun x => g' (liftT x) k := by
    intro k
    apply ae_eq_of_integral_contDiff_smul_eq (hg.locInt_grad k) (hg'.locInt_grad k)
    intro φ hφ hφc
    have h1 := hg.ibp φ hφ hφc k
    have h2 := hg'.ibp φ hφ hφc k
    simp only [smul_eq_mul]
    have e1 : ∫ x, φ x * g (liftT x) k = ∫ x, g (liftT x) k * φ x := by simp_rw [mul_comm]
    have e2 : ∫ x, φ x * g' (liftT x) k = ∫ x, g' (liftT x) k * φ x := by simp_rw [mul_comm]
    rw [e1, e2]
    linarith
  have hall : ∀ᵐ x ∂(volume : Measure (ι → ℝ)), ∀ k, g (liftT x) k = g' (liftT x) k :=
    ae_all_iff.mpr hk
  filter_upwards [ae_of_ae_liftT (p := fun y => ∀ k, g y k = g' y k) hall] with y hy
  funext k
  exact hy k

/-- The weighted Sobolev space `H^1(P)` on the torus `𝕋^ι`. -/
def MemH1 (P : Measure (UnitAddTorus ι)) (f : UnitAddTorus ι → ℝ) : Prop :=
  HasWeakGrad f ∧ MemLp f 2 P ∧ MemLp (fun x => Real.sqrt (sqNorm (weakGrad f x))) 2 P

/-- The Dirichlet integral `∫ |∇f|² dP`, in `ℝ≥0∞`. -/
noncomputable def dirichlet (P : Measure (UnitAddTorus ι)) (f : UnitAddTorus ι → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (sqNorm (weakGrad f x)) ∂P

/-! ### Configuration spaces -/

variable {N d : ℕ}

/-- `H^1(P)` on `(𝕋^d)^N`, through the identification with `𝕋^{N × d}`. -/
def MemH1C (P : Measure (Config N d)) (f : Config N d → ℝ) : Prop :=
  MemH1 (P.map flat) (f ∘ unflat)

/-- The weak partial gradient `∇_i f (X) ∈ ℝ^d` on `(𝕋^d)^N`: component `k` of `∇_i f`. -/
noncomputable def weakGradC (f : Config N d → ℝ) (X : Config N d) (i : Fin N) (k : Fin d) : ℝ :=
  weakGrad (f ∘ unflat) (flat X) (i, k)

/-- `∑ᵢ |∇ᵢ f (X)|²`, the squared full product gradient. -/
noncomputable def gradSqC (f : Config N d → ℝ) (X : Config N d) : ℝ :=
  ∑ i, ∑ k, weakGradC f X i k ^ 2

end SharpLSI
