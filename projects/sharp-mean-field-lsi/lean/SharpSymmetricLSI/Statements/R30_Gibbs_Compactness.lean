import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Paper.GroundT17
import SharpSymmetricLSI.Paper.Prop21Conclusion
import SharpSymmetricLSI.Statements.R03_Prop_2_2
import SharpSymmetricLSI.Statements.R19_Lemma_5_2
import SharpSymmetricLSI.Statements.R20_Lemma_5_3

/-!
# R30: Section 7.2, ground-state transformation and preservation of mass

Manuscript Section 7.2, (7.6)–(7.10). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a
reference eigenbasis, `Q = Q_T`, `γ_∞ = gammaInfOf W μ Q`, `p_N = K_N^{-1} e^{-U_N}`.
* (7.6)–(7.7): `Ψ_N = f_N √p_N` is an isometry `L²(P_N) → L²(μ^{⊗N})`, `Ψ_N ∈ H^1(μ^{⊗N})`, and
  `∫|∇Ψ_N|² dμ^{⊗N} ≤ C(ℰ_N(f_N) + ‖f_N‖²_{L²(P_N)})` for symmetric `f_N ∈ H^1(P_N)`.
* For `f_N` with the bound (2.5): after extraction, `f_N` and every fixed collection of
  fluctuations converge jointly in law under `P_N` to `(f, z_1, …, z_J)` under `γ_∞` for some
  `f ∈ L²(γ_∞)` ((7.8) and the joint convergence paragraph); `f_N²` is uniformly integrable;
  and (7.10) `∫ f_N² dP_N → ∫ f² dγ_∞`, `∫ f_N dP_N → ∫ f dγ_∞`.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- (7.6)–(7.7): the ground-state transformation. -/
theorem ground_state_transform {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f → IsSymmetric f →
      let Ψ : Config N d → ℝ := fun X =>
        f X * Real.sqrt (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N)
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ ∧
      ∫⁻ X, ENNReal.ofReal (Ψ X ^ 2) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N ∧
      ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal C * (energy V W N f + ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) := by
  obtain ⟨a₀, CF, -, hF⟩ := force_exponential hd hyp hr hμ
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr1
  obtain ⟨B, hB⟩ := prop_defective hd hyp hr r hrpos hr2
  exact ground_state_transform_of hyp hμ (CF := CF)
    (fun N hN ν h1 h2 h3 => ((hF N hN).2 ν h1 h2 h3).1) hrpos hB

/-- Section 7.2: compactness, joint convergence, uniform integrability, (7.10). -/
theorem gibbs_compactness {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (f : (k : ℕ) → Config (Ns k) d → ℝ)
    (hf : ∀ k, MemH1C (gibbs V W (Ns k)) (f k) ∧ IsSymmetric (f k))
    (hB : ∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (f k X ^ 2) ∂gibbs V W (Ns k)) + energy V W (Ns k) (f k) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : (ℕ → ℝ) → ℝ, MemLp F 2 (gammaInfOf W μ Q) ∧
      (∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
        Tendsto (fun k => ∫ X, g (f (φ k) X, fun n => fluct e (Ns (φ k)) n X)
            ∂gibbs V W (Ns (φ k))) atTop
          (𝓝 (∫ z, g (F z, fun n => z n) ∂gammaInfOf W μ Q))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
        ∫⁻ X in {X | M < f (φ k) X ^ 2}, ENNReal.ofReal (f (φ k) X ^ 2) ∂gibbs V W (Ns (φ k))
          ≤ ENNReal.ofReal ε) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ^ 2 ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, F z ^ 2 ∂gammaInfOf W μ Q)) ∧
      Tendsto (fun k => ∫ X, f (φ k) X ∂gibbs V W (Ns (φ k))) atTop
        (𝓝 (∫ z, F z ∂gammaInfOf W μ Q)) := by
  obtain ⟨a₀, CF, -, hF⟩ := force_exponential hd hyp hr hμ
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr1
  obtain ⟨B0, hB0⟩ := prop_defective hd hyp hr r hrpos hr2
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  exact gibbs_compactness_of hyp (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ)
    he hQ ⟨Cp, p, hp, fun N hN => ⟨(hCp N hN).2.1, (hCp N hN).2.2⟩⟩ (CF := CF)
    (fun N hN ν h1 h2 h3 => ((hF N hN).2 ν h1 h2 h3).1) hrpos hB0 Ns hNs f hf hB

end SharpLSI
