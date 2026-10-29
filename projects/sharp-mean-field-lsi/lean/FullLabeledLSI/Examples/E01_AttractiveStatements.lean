import FullLabeledLSI.Statements.S01_Theorem_1_1
import FullLabeledLSI.Statements.S04_Prop_2_3
import FullLabeledLSI.Statements.S14_Linearization
import FullLabeledLSI.Defs.F07_Sanity
import SharpSymmetricLSI.Defs.D12_Cosine

/-!
# Examples E1: statements for Section 9 of the full-labeled note (DRAFT, NOT YET COMPILED, NOT FROZEN)

Source: `manuscript/examples/sharp_full_labeled_lsi_public_20261004T170742Z_section9_examples_6299e22.tex`
(Section 9, "Examples of agreement for attractive interactions", added in commit 6299e22 of
DGR-Partition-Functions).  Every statement below carries `sorry`; the file is a statement layer for
Matt's sign-off and for the separate-context TeX-alignment review.  Nothing here edits a frozen file.

Conventions (as in `FullLabeledLSI`): the circle is `Torus 1`, `m = haar 1`, `V = 0`, constants live
in `ℝ≥0∞`.  The attractive interaction of Section 9 is `W(x,y) = C(0) - C(x-y)` (9.1), `C` smooth,
even, `∫ C dm = 0`.  `λ_G` is `lamG (lamShift lam) C` for a reference eigenbasis `(e, lam)` of the
Haar measure and `C = (I+T)^{-1}`, quantified over all such data as in S04 and S14.

TeX numbering (Theorem counter of Section 9, in order of appearance): Lemma 9.1 Fourier entropy bound;
Proposition 9.2 first attractive cosine; Lemma 9.3 second-mode remainder; Proposition 9.4 second
harmonic interval; Lemma 9.5 attained deficit; Lemma 9.6 uniform uniqueness; Proposition 9.7 near the
critical coupling; Lemma 9.8 concavity of the interaction excess; Lemma 9.9 scalar quotient attainment;
Proposition 9.10 equality below the Gaussian rate; Lemma 9.11 the Fourier concavity estimate.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL
namespace Ex

/-! ### Notation -/

/-- Haar measure on the circle as a probability measure (the uniform density `m`). -/
noncomputable def haarPM : ProbabilityMeasure (Torus 1) := ⟨haar 1, haar_isProbabilityMeasure 1⟩

/-- `V = 0`. -/
def zeroV : Torus 1 → ℝ := fun _ => 0

/-- `cos(2π k x)` on `𝕋 = 𝕋^1` (real part of `e^{2πikx}`). -/
noncomputable def cosMode (k : ℕ) (x : Torus 1) : ℝ := (fourier (k : ℤ) (x 0)).re

/-- `C(x) = 2a cos(2π k x)` (9.9), (9.12) and, with `k = 2`, the kernel of Proposition 9.4. -/
noncomputable def harmKernel (k : ℕ) (a : ℝ) (x : Torus 1) : ℝ := 2 * a * cosMode k x

/-- `W(x,y) = C(0) - C(x-y)` (9.1). -/
def attrW (C : Torus 1 → ℝ) (x y : Torus 1) : ℝ := C 0 - C (x - y)

/-- The Poisson-type kernel of (9.28):
`C(x) = 16 ((1-r²)/(1-2r cos(4πx)+r²) - 1)`, `r = 1/100`. -/
noncomputable def poissonKernel (x : Torus 1) : ℝ :=
  16 * ((1 - (1 / 100 : ℝ) ^ 2) / (1 - 2 * (1 / 100 : ℝ) * cosMode 2 x + (1 / 100 : ℝ) ^ 2) - 1)

/-- A representative in `ℝ` of a point of the circle (used only to differentiate periodic functions). -/
noncomputable def rep (x : Torus 1) : ℝ := (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (x 0)).choose

/-- Classical derivative of a function on the circle, read through its periodic lift. -/
noncomputable def dT (f : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  deriv (fun t : ℝ => f (liftT (fun _ : Fin 1 => t))) (rep x)

/-- `(g * ρ)(x) = ∫ g(x-y) ρ(y) dm(y)` for a density `ρ`. -/
noncomputable def convT (g ρ : Torus 1 → ℝ) (x : Torus 1) : ℝ := ∫ y, g (x - y) * ρ y ∂haar 1

/-- `λ_G` of the interaction `W` at Haar measure equals `v`, for every reference eigenbasis and
inverse covariance, and such data exist (so the statement is not vacuous). -/
def LamGValue (W : Torus 1 → Torus 1 → ℝ) (v : ℝ≥0∞) : Prop :=
  (∃ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (C : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam ∧ IsInverseOfIPlus (Tmat W (haar 1) e) C) ∧
    ∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (C : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat W (haar 1) e) C →
        lamG (lamShift lam) C = v

/-- The shared conclusion of Propositions 9.2, 9.4, 9.7 (the common value `ℓ` of `r_ms`, `r_*`,
`λ_G`) together with the equality of the two particle limits (Theorem 1.1, the symmetric limit,
and the remark closing Section 9.2). -/
def AgreementAt (W : Torus 1 → Torus 1 → ℝ) (ℓ : ℝ) : Prop :=
  rMs zeroV W = ENNReal.ofReal ℓ ∧ rStar zeroV W = ENNReal.ofReal ℓ ∧
    LamGValue W (ENNReal.ofReal ℓ) ∧
    Tendsto (fun N => rAll zeroV W N) atTop (𝓝 (ENNReal.ofReal ℓ)) ∧
    Tendsto (fun N => rSym zeroV W N) atTop (𝓝 (ENNReal.ofReal ℓ))

/-- Haar measure is the unique free-energy minimizer. -/
def HaarUniqueMinimizer (W : Torus 1 → Torus 1 → ℝ) : Prop :=
  IsMinimizer zeroV W haarPM ∧ ∀ μ : ProbabilityMeasure (Torus 1), IsMinimizer zeroV W μ → μ = haarPM

/-! ### 9.1 Convolution identities and a Fourier entropy bound -/

/-- Lemma 9.1, (9.6): `H(ρ|m) ≥ |∫ e^{2πikx} ρ dm|²` for every probability density `ρ` and `k ≥ 1`. -/
theorem fourier_entropy_bound {k : ℕ} (hk : 1 ≤ k) (ρ : Torus 1 → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    ENNReal.ofReal (Complex.normSq (∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1)) ≤
      klDiv (densMeasure ρ) (haar 1) := by
  sorry

/-! ### 9.2 The first attractive cosine -/

/-- Proposition 9.2, (9.7)-(9.9): `C = 2a cos(2πx)`, `0 ≤ a < 1`. Haar is the unique equilibrium,
`F_* = a`, and `r_ms = r_* = λ_G = 4π²(1-a)`; the particle limits both equal `4π²(1-a)`. -/
theorem first_attractive_cosine {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HaarUniqueMinimizer (attrW (harmKernel 1 a)) ∧ Fstar zeroV (attrW (harmKernel 1 a)) = (a : EReal) ∧
      AgreementAt (attrW (harmKernel 1 a)) (aCos * (1 - a)) := by
  sorry

/-! ### 9.3 Higher attractive harmonics -/

/-- Lemma 9.3, (9.18): for `ρ` with `√ρ ∈ H¹(m)`,
`I(ρ|m)/(4π²) - 2 H(ρ|m) ≥ (12/11) |∫ e^{4πix} ρ dm|²`, written without subtraction in `ℝ≥0∞`
(`aCos = 4π²`). -/
theorem second_mode_remainder (ρ : Torus 1 → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    ENNReal.ofReal (2 * aCos) * klDiv (densMeasure ρ) (haar 1) +
        ENNReal.ofReal (12 / 11 * aCos * Complex.normSq (∫ x, fourier 2 (x 0) * (ρ x : ℂ) ∂haar 1)) ≤
      fisherInfo (densMeasure ρ) (haar 1) := by
  sorry

/-- Proposition 9.4, (9.21): `C = 2a cos(4πx)`, `0 ≤ a ≤ 6/77`: `r_ms = r_* = λ_G = 4π²`.
Also Haar is the unique equilibrium (Section 9.3, first paragraph, from Lemma 9.1) and the particle
limits agree (closing remark of Section 9.3). -/
theorem second_harmonic_small {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 6 / 77) :
    HaarUniqueMinimizer (attrW (harmKernel 2 a)) ∧ AgreementAt (attrW (harmKernel 2 a)) aCos := by
  sorry

/-- The deficit `D_θ - 2r G_θ` of a finite family, in real form (finite for admissible families by
`msGap_msDiss_lt_top`). -/
noncomputable def deficit (W : Torus 1 → Torus 1 → ℝ) (r : ℝ) (F : Family 1) : ℝ :=
  (msDiss zeroV W F).toReal - 2 * r * (msGap zeroV W F).toReal

/-- The common one-site potential `A` of (9.18) for `C = 2a cos(2πkx)`:
`A = 4 C''*ρ̄ + (C'*ρ̄)² - 2 C'*(ρ̄ (C'*ρ̄)) + 2r C*ρ̄`. -/
noncomputable def commonPotential (C : Torus 1 → ℝ) (r : ℝ) (ρbar : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  4 * convT (dT (dT C)) ρbar x + (convT (dT C) ρbar x) ^ 2 -
    2 * convT (dT C) (fun y => ρbar y * convT (dT C) ρbar y) x + 2 * r * convT C ρbar x

/-- The one-site functional of (9.17): `q ↦ I(q|m) - 2r H(q|m) + ∫ A q dm`, real form. -/
noncomputable def oneSite (r : ℝ) (A q : Torus 1 → ℝ) : ℝ :=
  (fisherInfo (densMeasure q) (haar 1)).toReal - 2 * r * (klDiv (densMeasure q) (haar 1)).toReal +
    ∫ x, A x * q x ∂haar 1

/-- Lemma 9.5, (9.24)-(9.27): for `C = 2a cos(2πkx)`, `0 ≤ a < 1`, `0 < r < 4π²`, the infimum of the
deficit over admissible finite families is attained, by a family with at most six species; at any
minimizer every species density globally minimizes the one-site functional with potential
`A = commonPotential` of the average density, is smooth and strictly positive, and `f = √q` solves
`-4 f'' + A f - 4 r f log f = η f` with `η` the common minimum value. -/
theorem harmonic_deficit_attainment {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < aCos) :
    ∃ F : Family 1, F.Admissible ∧ F.q ≤ 6 ∧
      (∀ G : Family 1, G.Admissible → deficit (attrW (harmKernel k a)) r F ≤
        deficit (attrW (harmKernel k a)) r G) ∧
      ∀ G : Family 1, G.Admissible →
        deficit (attrW (harmKernel k a)) r G = (⨅ H : {H : Family 1 // H.Admissible},
            deficit (attrW (harmKernel k a)) r H.1) →
        (∀ i, ∀ q : Torus 1 → ℝ, (∀ x, 0 ≤ q x) → ∫ x, q x ∂haar 1 = 1 →
            MemH1 (haar 1) (fun x => Real.sqrt (q x)) →
          oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) ≤
            oneSite r (commonPotential (harmKernel k a) r G.bar) q) ∧
        (∀ i, ∃ f : Torus 1 → ℝ, IsSmoothT f ∧ (∀ x, 0 < f x) ∧
          (fun x => f x ^ 2) =ᵐ[haar 1] G.ρ i ∧
          ∃ η : ℝ, η = oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) ∧
            ∀ x : Torus 1,
              -4 * dT (dT f) x + commonPotential (harmKernel k a) r G.bar x * f x -
                  4 * r * f x * Real.log (f x) = η * f x) := by
  sorry

/-- The functional `S_{r,A}(f) = 4∫|f'|² dm + ∫ A f² dm - 2r H(f²|m)` of (9.20). -/
noncomputable def sFunctional (r : ℝ) (A : Torus 1 → ℝ) (f : Torus 1 → ℝ) : ℝ :=
  4 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 + ∫ x, A x * f x ^ 2 ∂haar 1 -
    2 * r * (klDiv (densMeasure (fun x => f x ^ 2)) (haar 1)).toReal

/-- `f` is a minimizer of `S_{r,A}` over `f ≥ 0`, `f ∈ H¹(m)`, `∫ f² dm = 1`. -/
def IsSMin (r : ℝ) (A : Torus 1 → ℝ) (f : Torus 1 → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ MemH1 (haar 1) f ∧ ∫ x, f x ^ 2 ∂haar 1 = 1 ∧
    ∀ g : Torus 1 → ℝ, (∀ x, 0 ≤ g x) → MemH1 (haar 1) g → ∫ x, g x ^ 2 ∂haar 1 = 1 →
      sFunctional r A f ≤ sFunctional r A g

/-- Lemma 9.6, (9.29): for every compact set `𝒜` of real potentials in `C(𝕋)` there is `ε > 0` such
that `S_{r,A}` has a unique minimizer for all `A ∈ 𝒜` and `0 ≤ r < ε`. Uniqueness is as elements
of `L²(m)` (almost everywhere); existence is part of the claim. -/
theorem harmonic_small_rate_uniqueness (𝒜 : Set C(Torus 1, ℝ)) (h𝒜 : IsCompact 𝒜) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A ∈ 𝒜, ∀ r : ℝ, 0 ≤ r → r < ε →
      ∃ f : Torus 1 → ℝ, IsSMin r (fun x => A x) f ∧
        ∀ g : Torus 1 → ℝ, IsSMin r (fun x => A x) g → g =ᵐ[haar 1] f := by
  sorry

/-- Proposition 9.7, (9.30): for every fixed integer `k ≥ 2` there is `a_k ∈ [1 - k⁻², 1)` such that
for `C = 2a cos(2πkx)` and `a_k < a < 1`: `r_ms = r_* = λ_G = 4π² k² (1-a)`. Also Haar is the unique
equilibrium and the particle limits agree (closing remark). `a_k` is not explicit. -/
theorem higher_near_critical {k : ℕ} (hk : 2 ≤ k) :
    ∃ ak : ℝ, 1 - 1 / (k : ℝ) ^ 2 ≤ ak ∧ ak < 1 ∧ ∀ a : ℝ, ak < a → a < 1 →
      HaarUniqueMinimizer (attrW (harmKernel k a)) ∧
        AgreementAt (attrW (harmKernel k a)) (aCos * (k : ℝ) ^ 2 * (1 - a)) := by
  sorry

/-! ### 9.4 An equality example with a nonlinear optimizer -/

/-- A finite signed measure `α - β` is encoded by a pair of finite measures (`α`, `β`); this is the
Fourier coefficient `σ̂(n) = ∫ e^{-2πinx} d(α-β)`. -/
noncomputable def sigmaHat (α β : Measure (Torus 1)) (n : ℤ) : ℂ :=
  ∫ x, fourier (-n) (x 0) ∂α - ∫ x, fourier (-n) (x 0) ∂β

/-- `Q_C(σ) = ∑_{k≠0} 4π²k² Ĉ(k) |σ̂(k)|²` (9.15), for a pair `(α, β)` encoding `σ = α - β`;
`Ĉ(k) = ∫ C e^{-2πikx} dm`. -/
noncomputable def QC (C : Torus 1 → ℝ) (α β : Measure (Torus 1)) : ℝ :=
  ∑' n : {n : ℤ // n ≠ 0},
    aCos * (n.1 : ℝ) ^ 2 * (∫ x, fourier (-n.1) (x 0) * (C x : ℂ) ∂haar 1).re *
      Complex.normSq (sigmaHat α β n.1)

/-- Evaluate `∫ f d(α - β)`. -/
noncomputable def intS (f : Torus 1 → ℝ) (α β : Measure (Torus 1)) : ℝ := ∫ x, f x ∂α - ∫ x, f x ∂β

/-- `(g * σ)(x) = ∫ g(x-y) dσ(y)` for `σ = α - β`. -/
noncomputable def convS (g : Torus 1 → ℝ) (α β : Measure (Torus 1)) (x : Torus 1) : ℝ :=
  intS (fun y => g (x - y)) α β

/-- The interaction contribution `𝒰_ℓ(ρ)` of (9.14), extended to `ρ = α - β` by polynomial
expansion: `2∫ C''*ρ dρ + ∫ |C'*ρ|² dρ + ℓ ∫ C*ρ dρ`. -/
noncomputable def Uint (C : Torus 1 → ℝ) (ℓ : ℝ) (α β : Measure (Torus 1)) : ℝ :=
  2 * intS (fun x => convS (dT (dT C)) α β x) α β + intS (fun x => convS (dT C) α β x ^ 2) α β +
    ℓ * intS (fun x => convS C α β x) α β

/-- Second derivative at `s = 0⁺` of `s ↦ 𝒰_ℓ(ρ + sσ)` for `ρ` a probability and `σ = α₁ - β₁`:
the Hessian `𝒰_ℓ''(ρ)[σ,σ]` of (9.15). -/
noncomputable def UintHess (C : Torus 1 → ℝ) (ℓ : ℝ) (ρ α₁ β₁ : Measure (Torus 1)) : ℝ :=
  iteratedDerivWithin 2
    (fun s : ℝ => Uint C ℓ (ρ + ENNReal.ofReal s • α₁) (ENNReal.ofReal s • β₁)) (Set.Ici 0) 0

/-- Concavity of `𝒰_ℓ` on probability measures, along mixtures. -/
def UintConcave (C : Torus 1 → ℝ) (ℓ : ℝ) : Prop :=
  ∀ (ρ₀ ρ₁ : Measure (Torus 1)), IsProbabilityMeasure ρ₀ → IsProbabilityMeasure ρ₁ →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (1 - t) * Uint C ℓ ρ₀ 0 + t * Uint C ℓ ρ₁ 0 ≤
        Uint C ℓ (ENNReal.ofReal (1 - t) • ρ₀ + ENNReal.ofReal t • ρ₁) 0

/-- Smooth, even, mean-zero kernel `C` (standing hypotheses of Section 9.4). -/
structure GoodKernel (C : Torus 1 → ℝ) : Prop where
  smooth : IsSmoothT C
  even : ∀ x, C (-x) = C x
  meanZero : ∫ x, C x ∂haar 1 = 0

/-- Lemma 9.8, first part: if Haar minimizes the free energy and `𝒰_{r_*}` is concave, then
`r_ms = r_*`. Here `ℓ` is a real number with `r_* = ofReal ℓ` (`r_*` is finite for smooth kernels,
which the proof establishes). -/
theorem interaction_concavity {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : rStar zeroV (attrW C) = ENNReal.ofReal ℓ)
    (hconc : UintConcave C ℓ) : rMs zeroV (attrW C) = rStar zeroV (attrW C) := by
  sorry

/-- Lemma 9.8, quantitative part (9.15), (9.16): if `Ĉ(k) ≥ 0`, `γ ≥ 0` and
`𝒰''_{r_*}(ρ)[σ,σ] ≤ -γ Q_C(σ)` for every probability `ρ` and every `σ = α₁ - β₁` of mass zero, then every
admissible finite family satisfies
`D_θ - 2 r_* G_θ ≥ ∑ θ_a [D(ρ_a) - 2 r_* G(ρ_a)] + (γ/2) ∑ θ_a Q_C(ρ_a - ρ̄) ≥ 0`
(real form; the species terms use the one-species `dissipation`, `gap`). -/
theorem interaction_compensation {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re)
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : rStar zeroV (attrW C) = ENNReal.ofReal ℓ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hhess : ∀ (ρ α₁ β₁ : Measure (Torus 1)), IsProbabilityMeasure ρ → IsFiniteMeasure α₁ →
      IsFiniteMeasure β₁ → α₁ Set.univ = β₁ Set.univ →
        UintHess C ℓ ρ α₁ β₁ ≤ -γ * QC C α₁ β₁)
    (F : Family 1) (hF : F.Admissible) :
    deficit (attrW C) ℓ F ≥
        ∑ a, F.θ a * ((dissipation zeroV (attrW C) (F.ρ a)).toReal -
            2 * ℓ * (gap zeroV (attrW C) (densMeasure (F.ρ a))).toReal) +
          γ / 2 * ∑ a, F.θ a *
            QC C (densMeasure (F.ρ a)) (densMeasure F.bar) ∧
      ∑ a, F.θ a * ((dissipation zeroV (attrW C) (F.ρ a)).toReal -
            2 * ℓ * (gap zeroV (attrW C) (densMeasure (F.ρ a))).toReal) +
          γ / 2 * ∑ a, F.θ a *
            QC C (densMeasure (F.ρ a)) (densMeasure F.bar) ≥ 0 := by
  sorry

/-- Lemma 9.9, parts (i) and (ii) (the last sentence of the lemma and `r_* > 0`): for a good kernel with
`Ĉ(k) ≥ 0`, `sup_{k≠0} Ĉ(k) < 1`, Haar the unique free-energy minimizer and the only density of zero
dissipation: (i) `r_* > 0`; (ii) if `r_* < λ_G` (for every reference eigenbasis datum) then `r_*` is
attained at a smooth, strictly positive, nonuniform admissible density.  The middle sentence of the lemma
(minimizing sequences) is `scalar_quotient_minimizing_sequence` below. -/
theorem scalar_quotient_attainment {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re ≤ 1 - δ)
    (huniq : HaarUniqueMinimizer (attrW C))
    (hzero : ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      dissipation zeroV (attrW C) ρ = 0 → ρ =ᵐ[haar 1] fun _ => 1) :
    0 < rStar zeroV (attrW C) ∧
      (∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
          IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
          rStar zeroV (attrW C) < lamG (lamShift lam) Cm →
        ∃ ρ : Torus 1 → ℝ, IsSmoothT ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
          ¬ (ρ =ᵐ[haar 1] fun _ => 1) ∧ 0 < gap zeroV (attrW C) (densMeasure ρ) ∧
          dissipation zeroV (attrW C) ρ =
            2 * rStar zeroV (attrW C) * (gap zeroV (attrW C) (densMeasure ρ)).toENNReal) := by
  sorry

/-- Lemma 9.9, middle sentence: under the hypotheses of `scalar_quotient_attainment`, every minimizing
sequence of admissible densities for the scalar quotient `D/(2G)` has a subsequence whose square roots
converge uniformly and weakly in `H¹(m)` to a limit `f`, and either `f²` is admissible and attains `r_*`
at positive gap, or `f = 1` and the limiting quotient (`= r_*`) is at least `λ_G`.  Weak convergence in
`H¹(m)` is tested against every `g ∈ H¹(m)` with the `H¹` inner product `∫ f g + ∫ f' g'`.
Each `ρ n` is taken to be its continuous representative (`hρc`), as the TeX tacitly does: admissibility
and the quotient do not see null sets, so uniform convergence of `√(ρ n)` would otherwise fail. -/
theorem scalar_quotient_minimizing_sequence {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re ≤ 1 - δ)
    (huniq : HaarUniqueMinimizer (attrW C))
    (hzero : ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      dissipation zeroV (attrW C) ρ = 0 → ρ =ᵐ[haar 1] fun _ => 1)
    (ρ : ℕ → Torus 1 → ℝ) (hρ : ∀ n, SharpLSI.Admissible zeroV (attrW C) (ρ n))
    (hρc : ∀ n, Continuous (ρ n))
    (hmin : Tendsto (fun n => dissipation zeroV (attrW C) (ρ n) /
      (2 * (gap zeroV (attrW C) (densMeasure (ρ n))).toENNReal)) atTop (𝓝 (rStar zeroV (attrW C)))) :
    ∃ (φ : ℕ → ℕ) (f : Torus 1 → ℝ), StrictMono φ ∧ Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      ∫ x, f x ^ 2 ∂haar 1 = 1 ∧ MemH1 (haar 1) f ∧
      TendstoUniformly (fun n x => Real.sqrt (ρ (φ n) x)) f atTop ∧
      (∀ g : Torus 1 → ℝ, MemH1 (haar 1) g →
        Tendsto (fun n => ∫ x, Real.sqrt (ρ (φ n) x) * g x ∂haar 1 +
            ∫ x, weakGrad (fun y => Real.sqrt (ρ (φ n) y)) x 0 * weakGrad g x 0 ∂haar 1) atTop
          (𝓝 (∫ x, f x * g x ∂haar 1 + ∫ x, weakGrad f x 0 * weakGrad g x 0 ∂haar 1))) ∧
      ((SharpLSI.Admissible zeroV (attrW C) (fun x => f x ^ 2) ∧
          dissipation zeroV (attrW C) (fun x => f x ^ 2) =
            2 * rStar zeroV (attrW C) *
              (gap zeroV (attrW C) (densMeasure (fun x => f x ^ 2))).toENNReal) ∨
        ((∀ x, f x = 1) ∧
          ∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
            IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
              lamG (lamShift lam) Cm ≤ rStar zeroV (attrW C))) := by
  sorry

/-- Proposition 9.10, (9.39)-(9.41): for the kernel `poissonKernel` (`r = 1/100`):
`0 < r_ms = r_* < λ_G = 4π²`; the scalar infimum is attained at a smooth, strictly positive,
nonuniform density; and the two particle limits both equal `r_*`. -/
theorem nonlinear_equality :
    0 < rMs zeroV (attrW poissonKernel) ∧ rMs zeroV (attrW poissonKernel) = rStar zeroV (attrW poissonKernel) ∧
      rStar zeroV (attrW poissonKernel) < ENNReal.ofReal aCos ∧
      LamGValue (attrW poissonKernel) (ENNReal.ofReal aCos) ∧
      (∃ ρ : Torus 1 → ℝ, IsSmoothT ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
        ¬ (ρ =ᵐ[haar 1] fun _ => 1) ∧ 0 < gap zeroV (attrW poissonKernel) (densMeasure ρ) ∧
        dissipation zeroV (attrW poissonKernel) ρ =
          2 * rStar zeroV (attrW poissonKernel) *
            (gap zeroV (attrW poissonKernel) (densMeasure ρ)).toENNReal) ∧
      Tendsto (fun N => rAll zeroV (attrW poissonKernel) N) atTop (𝓝 (rStar zeroV (attrW poissonKernel))) ∧
      Tendsto (fun N => rSym zeroV (attrW poissonKernel) N) atTop (𝓝 (rStar zeroV (attrW poissonKernel))) := by
  sorry

/-- Lemma 9.11, (9.43): for the kernel `poissonKernel`, every probability measure `ρ`, every
`σ = α₁ - β₁` of mass zero and every `0 ≤ ℓ ≤ 4π²`: `𝒰''_ℓ(ρ)[σ,σ] ≤ -(19/250) Q_C(σ)`. -/
theorem analytic_concavity (ρ α₁ β₁ : Measure (Torus 1)) (hρ : IsProbabilityMeasure ρ)
    (hα : IsFiniteMeasure α₁) (hβ : IsFiniteMeasure β₁) (hm : α₁ Set.univ = β₁ Set.univ)
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ aCos) :
    UintHess poissonKernel ℓ ρ α₁ β₁ ≤ -(19 / 250) * QC poissonKernel α₁ β₁ := by
  sorry

end Ex
end SharpLSI.FL
