import SharpSymmetricLSI.Statements.R13_Lemma_4_1
import SharpSymmetricLSI.Paper.LocalStructure5
import SharpSymmetricLSI.Paper.LyapSchmidt21

/-!
# R14: Section 4.2, local structure of the minimizer set

Manuscript Section 4.2, "Local structure near a minimizer", (4.3)–(4.6). Fix a minimizer `μ`
(uniqueness not yet known), with density `p = elDensity V W μ` (R13), `A = I + T` on `L²_0(μ)`,
`E = ker A`.

`minSet_local_structure` (no assumption on `r_*`):
* `T` is selfadjoint and Hilbert–Schmidt on `L²_0(μ)` (kernel `K ∈ L²(μ⊗μ)`; that `K` is the
  kernel of `T` is R17);
* (4.4) `T : L²_0(μ) → W^{1,∞}(𝕋^d)` boundedly (the constant `C` is existential, so the sup
  metric is used for `LipschitzWith`; it is equivalent to the flat metric, `flatDist_comparison`);
* minimality gives `A ≥ 0`;
* `E` is finite-dimensional (an `L²(μ)`-orthonormal basis `φ_1, …, φ_n`).

`lyapunov_schmidt` (assuming `r_* > 0`), the conclusion of (4.5)–(4.6) and the text after them:
with `k(a) = ∑ aᵢ φᵢ ∈ E` (`a ∈ ℝ^n`), there are `ε > 0` and a map `a ↦ y(a)` into
`E^⊥ ∩ X`, `X = {h ∈ W^{1,∞} : μ(h) = 0}`, which is `C^∞` on the ball `|a| < ε` as a map into
`W^{1,∞}` (encoded through the pair `(y(a), ∇y(a)) ∈ L^∞(m) × L^∞(m)^d`), with `y(0) = 0`,
`Dy(0) = 0`, solving `P_{E^⊥} g(k + y(k)) = 0` (4.5), `g(h) = P_{μ,0}[log(1+h) + W*(μh)]` (4.3);
every point `μ(1 + k(a) + y(a))` of the graph is a minimizer (the reduced energy `φ` vanishes
near `0`); every minimizer in a weak neighbourhood of `μ` lies on the graph; the graph map is
a homeomorphism (weak topology) from the ball onto a neighbourhood of `μ` in `𝒮`; and its
derivative at `0`, as a map into `L²_0(μ)`, is the inclusion `E ↪ L²_0(μ)` (tangent space
`ker(I+T)`).

`minSet_topological_chart`: the corollary used by the contraction argument (R15): `𝒮` is, near
`μ`, homeomorphic to an open subset of `ℝ^n`, `n = dim ker(I+T)`.
-/

open MeasureTheory Metric
open scoped ContDiff

namespace SharpLSI

variable {d : ℕ}

/-- `h ∈ ker(I+T)` (as an element of `L²_0(μ)`). -/
def InKerIT (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (h : Torus d → ℝ) : Prop :=
  MemL20 μ h ∧ (fun x => h x + Top W μ h x) =ᵐ[μ] 0

/-- The projected first variation `g(h) = P_{μ,0}[log(1+h) + W*(μh)]` (manuscript (4.3)). -/
noncomputable def gLS (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (h : Torus d → ℝ)
    (x : Torus d) : ℝ :=
  (Real.log (1 + h x) + ∫ y, W x y * h y ∂μ) -
    ∫ x', (Real.log (1 + h x') + ∫ y, W x' y * h y ∂μ) ∂μ

/-- `φ` is an `L²(μ)`-orthonormal basis of `ker(I+T)`. -/
def IsKerBasis (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {n : ℕ}
    (φ : Fin n → Torus d → ℝ) : Prop :=
  (∀ i, InKerIT W μ (φ i)) ∧
  (∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) ∧
  (∀ h, InKerIT W μ h → ∃ a : Fin n → ℝ, h =ᵐ[μ] fun x => ∑ i, a i * φ i x)

/-- Section 4.2: selfadjointness, Hilbert–Schmidt, (4.4), `A ≥ 0`, `dim ker A < ∞`. -/
theorem minSet_local_structure {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    (∀ h₁ h₂, MemL20 μ h₁ → MemL20 μ h₂ →
      ∫ x, h₁ x * Top W μ h₂ x ∂(μ : Measure (Torus d)) =
        ∫ x, Top W μ h₁ x * h₂ x ∂(μ : Measure (Torus d))) ∧
    Integrable (fun p : Torus d × Torus d => centeredKernel W μ p.1 p.2 ^ 2)
      ((μ : Measure (Torus d)).prod (μ : Measure (Torus d))) ∧
    (∃ C : ℝ, ∀ h, MemL20 μ h →
      (∀ x, |Top W μ h x| ≤ C * Real.sqrt (∫ y, h y ^ 2 ∂(μ : Measure (Torus d)))) ∧
      LipschitzWith (C * Real.sqrt (∫ y, h y ^ 2 ∂(μ : Measure (Torus d)))).toNNReal
        (Top W μ h)) ∧
    (∀ h, MemL20 μ h → 0 ≤ secondVar W μ h) ∧
    ∃ n : ℕ, ∃ φ : Fin n → Torus d → ℝ, IsKerBasis W μ φ := by
  exact ⟨fun h₁ h₂ hh₁ hh₂ => Top_selfadjoint hyp _ hh₁ hh₂, centeredKernel_sq_integrable hyp _,
    Top_W1inf hyp _, fun h hh => secondVar_nonneg hyp hμ hh, exists_kerBasis hyp hμ⟩

/-- (4.5)–(4.6) and the text after them: the Lyapunov–Schmidt parametrization of `𝒮` near `μ`. -/
theorem lyapunov_schmidt {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis W μ φ) :
    let k : EuclideanSpace ℝ (Fin n) → Torus d → ℝ := fun a x => ∑ i, a i * φ i x
    let p := elDensity V W μ
    ∃ ε : ℝ, 0 < ε ∧ ∃ y : EuclideanSpace ℝ (Fin n) → Torus d → ℝ,
    ∃ Y : EuclideanSpace ℝ (Fin n) → Lp ℝ ⊤ (haar d) × (Fin d → Lp ℝ ⊤ (haar d)),
      -- `y(a) ∈ W^{1,∞}`, represented by `Y a = (y(a), ∇y(a))`
      (∀ a, HasWeakGrad (y a) ∧ ((Y a).1 : Torus d → ℝ) =ᵐ[haar d] y a ∧
        ∀ j, ((Y a).2 j : Torus d → ℝ) =ᵐ[haar d] fun x => weakGrad (y a) x j) ∧
      -- smooth into `W^{1,∞}`, `y(0) = 0`, `Dy(0) = 0`
      ContDiffOn ℝ ∞ Y (ball 0 ε) ∧ Y 0 = 0 ∧ fderiv ℝ Y 0 = 0 ∧
      -- `y(a) ∈ E^⊥ ∩ X`
      (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε, ∫ x, y a x ∂(μ : Measure (Torus d)) = 0 ∧
        ∀ i, ∫ x, y a x * φ i x ∂(μ : Measure (Torus d)) = 0) ∧
      -- (4.5): `P_{E^⊥} g(k + y(k)) = 0`
      (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε, ∃ b : Fin n → ℝ,
        gLS W μ (fun x => k a x + y a x) =ᵐ[(μ : Measure (Torus d))] fun x => ∑ i, b i * φ i x) ∧
      -- the graph consists of minimizers (reduced energy `≡ 0`)
      (∀ a ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε,
        (∀ x, 0 < 1 + k a x + y a x) ∧
        freeEnergy V W (densMeasure fun x => p x * (1 + k a x + y a x)) = Fstar V W) ∧
      -- homeomorphism onto a weak neighbourhood of `μ` in `𝒮`
      (∃ U : Set (ProbabilityMeasure (Torus d)), IsOpen U ∧ μ ∈ U ∧
        ∃ e : ball (0 : EuclideanSpace ℝ (Fin n)) ε ≃ₜ
            {ν : ProbabilityMeasure (Torus d) // ν ∈ U ∧ IsMinimizer V W ν},
          ∀ a, ((e a : ProbabilityMeasure (Torus d)) : Measure (Torus d)) =
            densMeasure fun x => p x * (1 + k a x + y a x)) ∧
      -- tangent space: the derivative at `0` into `L²_0(μ)` is the inclusion of `E`
      (∃ (Z : EuclideanSpace ℝ (Fin n) → Lp ℝ 2 (μ : Measure (Torus d)))
          (ι : EuclideanSpace ℝ (Fin n) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d))),
        (∀ a, (Z a : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] fun x => k a x + y a x) ∧
        (∀ a, (ι a : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] k a) ∧
        HasFDerivAt Z ι 0) := by
  exact lyapunov_schmidt_aux hyp hμ hφ hr

/-- Corollary used in R15: `𝒮` is locally homeomorphic (weak topology) to an open subset of
`ℝ^n`, `n = dim ker(I+T)`. -/
theorem minSet_topological_chart {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis W μ φ) :
    ∃ U : Set (ProbabilityMeasure (Torus d)), IsOpen U ∧ μ ∈ U ∧
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧
      Nonempty ({ν : ProbabilityMeasure (Torus d) // ν ∈ U ∧ IsMinimizer V W ν} ≃ₜ O) := by
  exact minSet_topological_chart_aux hyp hμ hφ hr

end SharpLSI
