import DGPS.Lipschitz.T01MobilityLimit
import SharpSymmetricLSI.Paper.FormLiminfS8b
import SharpSymmetricLSI.Paper.LocalStructure1

/-! Weighted empirical mobility errors for the actual particle law. -/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology
open SharpLSI SharpLSI.FL
open scoped ENNReal

variable {d : ℕ}

/-- The actual mobility error vanishes when paired with bounded L2 and L4 families. -/
theorem t01_mobility_weighted_error (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hac : (μ : Measure (Torus d)) ≪ haar d)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : SharpLSI.IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ SharpLSI.liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {p Bp : ℝ} (hp : 1 < p) (hBp : 0 ≤ Bp)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    (Ns : ℕ → ℕ+) (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop)
    {f H : (k : ℕ) → SharpLSI.Config (Ns k) d → ℝ}
    (hfm : ∀ k, AEStronglyMeasurable (f k) (particleLaw A (Ns k))) {B : ℝ}
    (hf2 : ∀ k, MemLp (f k) 2 (particleLaw A (Ns k)) ∧
      ∫ X, f k X ^ 2 ∂particleLaw A (Ns k) ≤ B) {K : ℝ}
    (hH : ∀ k, MemLp (H k) 4 (particleLaw A (Ns k)) ∧
      ∫ X, H k X ^ 4 ∂particleLaw A (Ns k) ≤ K) (i j : ℕ) :
    Tendsto (fun k => ∫ X, |f k X * H k X *
      (SharpLSI.mobA eC (Ns k) X i j - if i = j then lam (i + 1) else 0)|
        ∂particleLaw A (Ns k)) atTop (𝓝 0) := by
  let P (k : ℕ) := particleLaw A (Ns k)
  let D (k : ℕ) (X : SharpLSI.Config (Ns k) d) :=
    SharpLSI.mobA eC (Ns k) X i j - if i = j then lam (i + 1) else 0
  obtain ⟨hSm, M, hM⟩ := schroC_S_facts hφ (i + 1) (j + 1)
  let L : ℝ := M + |if i = j then lam (i + 1) else 0|
  have hDM : ∀ k X, |D k X| ≤ L := fun k X =>
    (abs_sub _ _).trans (add_le_add (SharpLSI.abs_mobA_le hM _ X) le_rfl)
  have hDm : ∀ k, Measurable (D k) := fun k =>
    (SharpLSI.measurable_mobA hφ (Ns k) i j).sub_const _
  have hDL : ∀ k, MemLp (D k) 2 (P k) := fun k =>
    MemLp.of_bound (hDm k).aestronglyMeasurable L (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]
      exact hDM k X)
  have hD2 : Tendsto (fun k => ∫ X, D k X ^ 2 ∂P k) atTop (𝓝 0) :=
    t01_mobility_particleLaw_L2_tendsto A μ hfix hac he hφ heC hp hBp hρ Ns hNs i j
  have hroot : Tendsto (fun k => Real.sqrt (∫ X, D k X ^ 2 ∂P k)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hD2.sqrt
  have habs : Tendsto (fun k => ∫ X, |D k X| ∂P k) atTop (𝓝 0) :=
    squeeze_zero (fun k => integral_nonneg fun X => abs_nonneg _)
      (fun k => SharpLSI.integral_abs_le_sqrt' (hDL k)) hroot
  exact SharpLSI.tendsto_weighted_err P hfm hf2 hH hDm hDM habs

end DGPS.Lipschitz
