import FullLabeledLSI.Defs.F02_Constants
import FullLabeledLSI.Paper.Sec5Perm
import FullLabeledLSI.Paper.Sec5Chain
import FullLabeledLSI.Paper.Sec5Products2
import FullLabeledLSI.Paper.Sec5ForceSum
import FullLabeledLSI.Paper.Sec5ForceRep
import FullLabeledLSI.Paper.Sec5ForceAE
import FullLabeledLSI.Paper.Sec5ForceJensen
import FullLabeledLSI.Paper.Sec5ForceT3
import FullLabeledLSI.Paper.Sec5CondD
import FullLabeledLSI.Paper.Sec5MFD
import SharpSymmetricLSI.Paper.Defective29

/-!
# Proposition 2.2 large-N assembly: definitions
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 0. Definitions -/

/-- `σ(X_S, X_i)`, the σ-algebra of the revealed coordinates and the current one (same term as in
`jensen_force`, `score_ae_eq_condExp`; `revealSigma` of S22 unfolds to it). -/
abbrev revSigma {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : MeasurableSpace (Config N d) :=
  MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance

/-- `Σ_i Σ_k ∫ s_{i,k}² dν`, the Fisher-information-type sum (real form). -/
noncomputable def fisherS {N : ℕ} (ν : Measure (Config N d)) (s : Fin N → Fin d → Config N d → ℝ) : ℝ :=
  ∑ i, ∑ k, ∫ X, s i k X ^ 2 ∂ν

/-- The test function `B(z) = K(z₀, z₁)/2` of `J(ρ) = ∫ B dρ^{⊗2}` (`Jfun_eq_pi`). -/
noncomputable def Bk (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) :
    (Fin 2 → Torus d) → ℝ :=
  fun z => centeredKernel W μ (z 0) (z 1) / 2

/-- `mfDiss ν s j`: the level-`j` mean-field dissipation
`E_{S,i} E_ν |E[s_i - G_i | X_S, X_i] + B_S(X_i)|²` (`G_i = Gpart`, `B_S = BS`), `avg1R`-averaged over the
uniform `j`-subset `S` and `i ∈ Sᶜ`. -/
noncomputable def mfDiss {N : ℕ} (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ)
    (ν : Measure (Config N d)) [IsFiniteMeasure ν] (s : Fin N → Fin d → Config N d → ℝ)
    (j : ℕ) : ℝ :=
  avg1R N j fun S i => ∫ X, ∑ k : Fin d,
    (condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X +
      BS bF ν S X (X i) k) ^ 2 ∂ν

/-- The reference logarithmic Sobolev inequality of `μ` with constant `A`
(the conclusion of `exists_klDiv_le_reference`, as a named `Prop`). -/
def RefLSI (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (A : ℝ) : Prop :=
  ∀ {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ}, Measurable ρ → IsWeakGrad ρ g →
    (∀ k, Measurable fun x => g x k) → (∀ k, MemLp (fun x => g x k) 2 (haar d)) →
    ∀ {c C : ℝ}, 0 < c → (∀ x, c ≤ ρ x) → (∀ x, ρ x ≤ C) → ∫ x, ρ x ∂haar d = 1 →
      klDiv (densMeasure ρ) μ ≤ ENNReal.ofReal A *
        ∫⁻ x, ENNReal.ofReal (ρ x * ∑ k, (g x k / ρ x + lipGrad (PhiMF V W μ) x k) ^ 2) ∂haar d

/-- **Data of the regularized law.**  `ν = Q·volume` with `c ≤ Q ≤ C`, weak gradient `GQ ∈ L²`, score
`s` (the score of `ν` relative to the Gibbs measure), the bounded particle-force representative
`Gpart bF bΔ`, and the a.e. relation `∇ log Q = s - G - ∇Φ_μ(X_i)` (this is `GQreg_flat_eq`).
Instantiated for `Q = Qreg V W n f`, `GQ = GQreg V W μ n f g`, `s = sfun n f g` by `scoreData_Qreg`. -/
structure ScoreData (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    {N : ℕ} (ν : Measure (Config N d)) (Q : Config N d → ℝ) (c C : ℝ)
    (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (s : Fin N → Fin d → Config N d → ℝ)
    (bF : Torus d → Torus d → Fin d → ℝ) (bΔ : Torus d → Fin d → ℝ) (Bb : ℝ) : Prop where
  eq : ν = qMeasure Q
  dens : IsBddDens Q c C
  gradW : IsWeakGrad (Q ∘ unflat) GQ
  gradM : ∀ p, Measurable fun y => GQ y p
  gradL2 : ∀ p, MemLp (fun y => GQ y p) 2 volume
  force : ForceRep bF bΔ Bb
  /-- `b = bF` a.e. (output of `exists_force_rep`). -/
  bF_ae : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, bForce W μ p.1 p.2 k = bF p.1 p.2 k
  /-- `∇_i U_N = G_i` a.e. (output of `exists_force_rep`). -/
  G_ae : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
    weakGradC (Ucentered W μ N) X i k = Gpart bF bΔ N X i k
  sM : ∀ i k, Measurable (s i k)
  sL2 : ∀ i k, Integrable (fun X => s i k X ^ 2) ν
  score : ∀ᵐ X ∂ν, ∀ i k, GQ (flat X) (i, k) / Q X =
    s i k X - Gpart bF bΔ N X i k - lipGrad (PhiMF V W μ) (X i) k


end SharpLSI.FL
