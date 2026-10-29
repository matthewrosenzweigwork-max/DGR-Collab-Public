import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D15_Forces
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Paper.LemmaA2_30

/-!
# R25: Lemma A.2 (`lem:kernel-approximation`), (6.4), (A.9)

Manuscript (6.4), Lemma A.2 and (A.9). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a
reference eigenbasis.
* `IsKernelApprox`: a sequence `K_R` of centered symmetric finite-rank kernels, each a finite
  sum `∑_{i,j∈s} a_{ij} e_i(x) e_j(y)` (`i, j ≥ 1`, `a` symmetric), with `K_R → K` uniformly and
  in `H^1(μ⊗μ)`, `sup_R (‖K_R‖_∞ + ‖∇K_R‖_∞) < ∞` (6.4); diagonal restrictions `K_R(x,x) → K(x,x)`
  uniformly with uniformly bounded weak gradients (Lemma A.2). Kernels are functions on
  `(𝕋^d)² = Config 2 d`; sup norms are `L^∞(μ⊗μ)` norms (the measures have positive continuous
  densities, so these are the uniform norms of the continuous kernels).
* (A.9): `Q = -log μ` is globally semiconvex (`D²Q ≥ -K_Q I` distributionally) and
  `Lip(P_t h) ≤ e^{K_Q t} Lip(h)` for the reference semigroup `P_t = e^{tL_μ}`, encoded through
  its spectral action `⟨P_t h, e_j⟩_μ = e^{-tλ_j} ⟨h, e_j⟩_μ`. `Lip` is for the flat (Euclidean)
  distance (`FlatLipschitzWith`): the Bochner argument controls the Euclidean gradient, and the
  sup-metric version is false in general (review of block 3).
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- A kernel as a function on `(𝕋^d)² = Config 2 d`. -/
def kerC (K : Torus d → Torus d → ℝ) (X : Config 2 d) : ℝ := K (X 0) (X 1)

/-- Finite-rank kernel approximation with uniform force bounds (manuscript (6.4), Lemma A.2). -/
def IsKernelApprox (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ)
    (KR : ℕ → Torus d → Torus d → ℝ) : Prop :=
  (∀ R, ∃ (s : Finset ℕ) (a : ℕ → ℕ → ℝ), (∀ i j, a i j = a j i) ∧
    ∀ x y, KR R x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y) ∧
  Tendsto (fun R => eLpNorm (fun X => kerC (KR R) X - kerC (centeredKernel W μ) X) ⊤
    (Measure.pi fun _ : Fin 2 => μ)) atTop (𝓝 0) ∧
  Tendsto (fun R => ∫⁻ X, ENNReal.ofReal ((kerC (KR R) X - kerC (centeredKernel W μ) X) ^ 2 +
      gradSqC (fun Y => kerC (KR R) Y - kerC (centeredKernel W μ) Y) X)
    ∂Measure.pi (fun _ : Fin 2 => μ)) atTop (𝓝 0) ∧
  (∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ R, eLpNorm (kerC (KR R)) ⊤ (Measure.pi fun _ : Fin 2 => μ) +
    eLpNorm (fun X => Real.sqrt (gradSqC (kerC (KR R)) X)) ⊤ (Measure.pi fun _ : Fin 2 => μ) ≤ B) ∧
  Tendsto (fun R => eLpNorm (fun x => KR R x x - centeredKernel W μ x x) ⊤ μ) atTop (𝓝 0) ∧
  (∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ R,
    eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad (fun z => KR R z z) x))) ⊤ μ ≤ B)

/-- (6.4) and Lemma A.2: such approximations exist. -/
theorem kernel_approximation {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ KR, IsKernelApprox W μ e KR :=
  kernel_approximation_aux hd hyp hμ he

/-- (A.9): semiconvexity of `Q = -log μ` and the Lipschitz bound for the reference semigroup. -/
theorem semigroup_lipschitz {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {p : Torus d → ℝ}
    (hp : (∀ x, 0 < p x) ∧ (μ : Measure (Torus d)) = densMeasure p)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ KQ : ℝ, 0 ≤ KQ ∧
      (∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
        ∀ ξ : Fin d → ℝ, -KQ * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
          ∫ x, -Real.log (p (liftT x)) * secondDirDeriv φ ξ x) ∧
      ∀ (t : ℝ), 0 ≤ t → ∀ (L : ℝ) (h : Torus d → ℝ), FlatLipschitzWith L h →
        ∃ g : Torus d → ℝ, FlatLipschitzWith (Real.exp (KQ * t) * L) g ∧
          ∀ j, ∫ x, g x * e j x ∂(μ : Measure (Torus d)) =
            Real.exp (-t * lam j) * ∫ x, h x * e j x ∂(μ : Measure (Torus d)) :=
  semigroup_lipschitz_aux hd hyp hμ hp he

end SharpLSI
