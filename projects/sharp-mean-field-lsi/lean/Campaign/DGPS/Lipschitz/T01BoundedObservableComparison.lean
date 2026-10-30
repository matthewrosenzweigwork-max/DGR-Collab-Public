import DGPS.Lipschitz.GaussianKernelTilt
import DGPS.Lipschitz.T01ReduceComparison
import DGPS.Lipschitz.T01FixedReferenceComparison
import DGPS.Lipschitz.T01RootReferenceBounds

/-! Joining the actual ground-state reduction and full reference comparison. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

set_option backward.isDefEq.respectTransparency.types false in
/-- For every bounded full-domain particle family, the actual entropy/energy lower comparison
follows from the proved same-rank replacement estimates. -/
theorem actual_bounded_family_comparison {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (S : Spec d) (aux : Aux S)
    (hfix : (frozenGibbs J (specProbability_LIP016 S)).measure = S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    (F : FiniteRankApprox J.W S.mu S.v) (CR : ℕ → ℕ → ℕ → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (hpos : ∀ R, PosIPlus F R σ)
    (hCR : ∀ R, IsInverseOfIPlus (F.a R) (CR R))
    {Kinf : ℝ} (hK0 : 0 < Kinf)
    (hKN : Tendsto (fun N : ℕ => centeredPartition J.W S.mu N) atTop (𝓝 Kinf))
    (hκ : Tendsto (fun R => kappaR F R) atTop (𝓝 Kinf))
    (hU : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
        eLpNorm (fun X => Ucentered J.W S.mu N X - URN F R N X) q (QN S.mu N)) atTop (𝓝 0))
    (hforce : ∀ η : ℝ, 0 < η → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N : ℕ+ in atTop,
      (∫⁻ X, ENNReal.ofReal (gradSqC
        (fun Y => centeredParticlePotential J (specProbability_LIP016 S) N Y - URN F R N Y) X)
          ∂particleLaw J N) ≤ ENNReal.ofReal η)
    {b0 : ℝ} (hb0 : 0 ≤ b0)
    (hbR : Tendsto (fun R => (bRate S.mu S.lam (CR R)).toReal) atTop (𝓝 b0))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ+, ∫ X, centeredParticleDensity J (specProbability_LIP016 S) N X ^ p
      ∂Measure.pi (fun _ : Fin N => S.mu) ≤ C)
    (B E0 : ℝ) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E0)
    (f : (N : ℕ+) → ParticleH1 J N) (hB : ∀ N X, |f N X| ≤ B)
    (hE : ∀ N, particleEnergy J N (f N) ≤ E0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ+ in atTop,
      -ε ≤ particleEnergy J N (f N) - b0 / 2 * (particleEntropy J N (f N)).toReal := by
  intro ε hε
  let μ := specProbability_LIP016 S
  obtain ⟨M, hM, hroot⟩ := centeredParticleRoot_uniform_reference_bounds J hJ aux.hd μ hfix
    hp hC0 hC
  let Ψ : (N : ℕ) → Config N d → ℝ := fun N =>
    if hN : 0 < N then centeredParticleRoot J μ ⟨N, hN⟩ (f ⟨N, hN⟩) else fun _ => 0
  have hΨ : ∀ N, 1 ≤ N → MemH1C (QN S.mu N) (Ψ N) ∧
      refEnergy S.mu (Ψ N) ≤ ENNReal.ofReal (2 * E0 + B ^ 2 * M / 2) ∧
      ∫⁻ X, ENNReal.ofReal (|Ψ N X| ^ (2 * p)) ∂QN S.mu N ≤ ENNReal.ofReal (B ^ (2 * p) * C) := by
    intro N hN
    have hn : 0 < N := hN
    simp only [Ψ, dif_pos hn]
    convert hroot B E0 hB0 hE0 (⟨N, hn⟩ : ℕ+) (f ⟨N, hn⟩)
      (hB ⟨N, hn⟩) (hE ⟨N, hn⟩) using 1 <;> rfl
  obtain ⟨R₀, hR₀⟩ := actual_reduce_J J hJ μ hfix he hC1 F CR hK0 hKN hκ hU hforce
    hb0 hbR hp hC0 hC B E0 hB0 hE0 (ε / 2) (by positivity)
  have href := fixed_reference_comparison S aux he hC1 hlam0 hlam1 F R₀ hσ (hpos R₀)
    (CR R₀) (hCR R₀) hp (by positivity) (by positivity) Ψ hΨ (ε / 2) (by positivity)
  filter_upwards [hR₀ R₀ le_rfl, tendsto_PNat_val_atTop_atTop.eventually href] with N hred hlo
  have hred' := hred (f N) (hB N) (hE N)
  simp only [Ψ, dif_pos N.pos] at hlo
  change -(ε / 2) ≤ Jexpr F S.lam (CR R₀) R₀ (centeredParticleRoot J μ N (f N)) at hlo
  calc
    -ε = -(ε / 2) - ε / 2 := by ring
    _ ≤ Jexpr F S.lam (CR R₀) R₀ (centeredParticleRoot J μ N (f N)) - ε / 2 :=
      sub_le_sub_right hlo (ε / 2)
    _ ≤ particleEnergy J N (f N) - b0 / 2 * (particleEntropy J N (f N)).toReal := hred'

end DGPS.Lipschitz
