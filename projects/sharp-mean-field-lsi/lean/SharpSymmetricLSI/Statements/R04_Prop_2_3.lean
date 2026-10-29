import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D18_GaussianForm
import SharpSymmetricLSI.Paper.FormLiminf12
import SharpSymmetricLSI.Paper.Prop23Final1
import SharpSymmetricLSI.Statements.R23_Reference_Spectrum

/-!
# R4: Proposition 2.3 (`prop:compactness`), Gaussian compactness and symmetric spectral gap

Manuscript Proposition 2.3, (2.4)–(2.8). Following the integrator's design notes, the
proposition is stated about the concrete objects of Sections 6 and 8: for the minimizer `μ`,
every reference eigenbasis `(e_j, λ_j)` (6.1), `C = (I+T)^{-1}` (6.11), every centered Gaussian
`γ_∞` on `ℝ^ℕ` with covariance `C` (Lemma 6.1), `ℰ_∞` the closure of (8.1), and `λ_G` of (8.9).
Existence of the eigenbasis, of `C` and of `γ_∞` is part of the conclusion. The existential
wording of Proposition 2.3 is the corollary `prop_compactness_exists`.

Encodings:
* "after extraction": a strictly increasing `φ : ℕ → ℕ`.
* convergence in law: `∫ g(f_N) dP_N → ∫ g(f) dγ_∞` for every bounded continuous `g`.
* uniform integrability of `f_N²` along the subsequence:
  `∀ ε > 0, ∃ M, ∀ k, ∫_{f_k² > M} f_k² dP_{N_k} ≤ ε` (the measures vary with `k`).
* "for every fixed Lipschitz `χ`": `χ : ℝ → ℝ` with `LipschitzWith L χ` for some `L`.
REVIEW.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- The compactness statement (2.5)–(2.7) of Proposition 2.3 for a given `γ_∞` and `ℰ_∞`. -/
def CompactnessProperty (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (γ : Measure (ℕ → ℝ))
    (EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞) : Prop :=
  ∀ (Ns : ℕ → ℕ), Tendsto Ns atTop atTop → ∀ f : (k : ℕ) → Config (Ns k) d → ℝ,
    (∀ k, MemH1C (gibbs V W (Ns k)) (f k) ∧ IsSymmetric (f k)) →
    (∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k)) + energy V W (Ns k) (f k) ≤ B) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ ∧
      (∀ g : ℝ →ᵇ ℝ, Tendsto (fun k => ∫ X, g (f (φ k) X) ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, g (F z) ∂γ))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
        ∫⁻ X in {X | M < f (φ k) X ^ 2}, ENNReal.ofReal (f (φ k) X ^ 2) ∂gibbs V W (Ns (φ k))
          ≤ ENNReal.ofReal ε) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ∂gibbs V W (Ns (φ k))) atTop (𝓝 (∫ z, F z ∂γ)) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ^ 2 ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, F z ^ 2 ∂γ)) ∧
      EInf F ≤ liminf (fun k => energy V W (Ns (φ k)) (f (φ k))) atTop ∧
      ∀ χ : ℝ → ℝ, (∃ L, LipschitzWith L χ) →
        EInf (χ ∘ F) ≤ liminf (fun k => energy V W (Ns (φ k)) (χ ∘ f (φ k))) atTop

/-- The properties (2.4)–(2.8) asserted by Proposition 2.3 for given `γ_∞`, `ℰ_∞`, `λ_G`. -/
def GaussianInputProperties (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (γ : Measure (ℕ → ℝ)) (EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞) (lG : ℝ≥0∞) : Prop :=
  rStar V W ≤ lG ∧
  (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
    ent γ (fun z => f z ^ 2) ≤ 2 / lG * EInf f ∧ var γ f ≤ EInf f / lG) ∧
  CompactnessProperty V W γ EInf ∧
  Tendsto (fun N => lamSym V W N) atTop (𝓝 lG)

/-- The conclusion of Proposition 2.3, about the concrete objects of Sections 6 and 8. -/
def CompactnessConclusion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
    (∃ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam) ∧
    ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      (∃ C, IsInverseOfIPlus (Tmat W μ e) C) ∧
      ∀ C, IsInverseOfIPlus (Tmat W μ e) C →
        (∃ γ, IsCenteredGaussianCov γ C) ∧
        ∀ γ, IsCenteredGaussianCov γ C →
          GaussianInputProperties V W γ (gaussForm (lamShift lam) γ) (lamG (lamShift lam) C)

/-- Proposition 2.3 (concrete form). -/
theorem prop_compactness {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    CompactnessConclusion V W :=
  prop_compactness_of_form hd hyp hr fun _μ hμ _e _lam he _C hC _γ hγ =>
    form_liminf_of hd hyp hr hμ he hC hγ

/-- Proposition 2.3 in the manuscript's existential wording: there exist a centered Gaussian
probability `γ_∞` on `ℝ^ℕ`, a form `ℰ_∞` (the closure of a gradient form (8.1) with weights
`λ_j > 0`), and `λ_G ≥ r_*` with properties (2.4)–(2.8). -/
def CompactnessExistsConclusion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∃ (C : ℕ → ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (lam' : ℕ → ℝ),
    IsCenteredGaussianCov γ C ∧ (∀ j, 0 < lam' j) ∧
    GaussianInputProperties V W γ (gaussForm lam' γ) (lamG lam' C)

/-- Proposition 2.3, existential wording. -/
theorem prop_compactness_exists {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    CompactnessExistsConclusion V W := by
  obtain ⟨⟨μ, hμ⟩, -, -⟩ := exists_minimizer hyp
  obtain ⟨⟨e, lam, he⟩, h2⟩ := prop_compactness hd hyp hr μ hμ
  obtain ⟨⟨C, hC⟩, h3⟩ := h2 e lam he
  obtain ⟨⟨γ, hγ⟩, h4⟩ := h3 C hC
  exact ⟨C, γ, lamShift lam, hγ,
    fun j => ((ref_spectrum hd hyp hr hμ).2 e lam he).1 (j + 1) (by omega), h4 γ hγ⟩

end SharpLSI
