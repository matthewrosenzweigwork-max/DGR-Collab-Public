import Mathlib
import DGPS.Examples.PositiveH1.TransferTailForm

/-!
# Common vanishing tail coefficient (H1033)

With `κ = 1/100`, `ε_M = 16 α_M² + κ A_M + 44 κ C_M → 0`, and for every `N ≥ 1`, `M ≥ 2`,
`f ∈ H¹(P_N)` both `∫ f² T_{N,M} dP_N` and `∫ f² |∇T_{N,M}|² dP_N` are bounded by
`ε_M (E_N(f) + ‖f‖₂²)`.  Combines H1030 and H1032 (all quantifiers over `N`, `M`, `f` are
independent of the cutoff `M`, so the coefficient depends on `M` alone).
-/

open MeasureTheory Filter Topology
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier

namespace DGPS.Examples.PositiveH1.Transfer

/-- The common tail coefficient `ε_M = 16 α_M² + κ A_M + 44 κ C_M` at `κ = 1/100`. -/
noncomputable def h1033_eps (M : ℕ) : ℝ :=
  16 * h1030_alpha M ^ 2 + (1 / 100) * tailA M + 44 * (1 / 100) * C M

theorem common_vanishing_tail_coefficient :
    Tendsto h1033_eps atTop (𝓝 0) ∧ ∀ (N : ℕ+) (M : ℕ), 2 ≤ M → ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      ∫ x, f x ^ 2 * tailT (1 / 100) N M x ∂particleLaw (kernelData (1 / 100)) N ≤
        h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
          ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N) ∧
      ∀ G, IsParticleHaarWeakGradient N (tailT (1 / 100) N M) G →
        ∫ x, f x ^ 2 * particleTangentNormSq (G x) ∂particleLaw (kernelData (1 / 100)) N ≤
          h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
            ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
  obtain ⟨hα, hF⟩ := uniform_force_tail_form_bound
  refine ⟨?_, fun N M _ f => ⟨?_, fun G hG => ?_⟩⟩
  · have h := (((hα.pow 2).const_mul 16).add (tendsto_tailA.const_mul (1 / 100 : ℝ))).add
      (tendsto_C.const_mul (44 * (1 / 100) : ℝ))
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h
    exact h
  · have hP := (positive_potential_tail_form_bound N M).2 f
    have hE := particleEnergy_nonneg f
    have hm : 0 ≤ ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N :=
      integral_nonneg fun x => sq_nonneg _
    have hA := h1030_tailA_nonneg M
    have hC := h1032_C_nonneg M
    unfold h1033_eps
    nlinarith [mul_nonneg hA hm, mul_nonneg hC hm, mul_nonneg hC hE, mul_nonneg hA hE,
      sq_nonneg (h1030_alpha M), mul_nonneg (sq_nonneg (h1030_alpha M)) hE,
      mul_nonneg (sq_nonneg (h1030_alpha M)) hm]
  · have hP := (hF N M).2 G hG |>.2 f
    have hE := particleEnergy_nonneg f
    have hm : 0 ≤ ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N :=
      integral_nonneg fun x => sq_nonneg _
    have hA := h1030_tailA_nonneg M
    have hC := h1032_C_nonneg M
    have hs : 0 ≤ particleEnergy (kernelData (1 / 100)) N f +
        ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N := by linarith
    unfold h1033_eps
    nlinarith [mul_nonneg hA hs, mul_nonneg hC hs]

end DGPS.Examples.PositiveH1.Transfer
