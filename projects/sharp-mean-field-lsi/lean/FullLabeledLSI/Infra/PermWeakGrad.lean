import SharpSymmetricLSI.Paper.Defective3
import SharpSymmetricLSI.Paper.R37Particle

/-!
# Weak gradients under permutations of the particle labels

`X ↦ X ∘ σ` on `Config N d` corresponds to the index reshuffling `(i,k) ↦ (σ i, k)` of the flat
torus; `isWeakGrad_perm` is `isWeakGrad_reidx` (Defective3) for this index equivalence:
`∇(F(· ∘ σ))_{(i,k)} = (∇F)(· ∘ σ)_{(σ⁻¹ i, k)}`.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace SharpLSI.FL

variable {N d : ℕ}

/-- The index equivalence `(i,k) ↦ (σ⁻¹ i, k)` of `Fin N × Fin d`. -/
def permIdx (σ : Equiv.Perm (Fin N)) : (Fin N × Fin d) ≃ (Fin N × Fin d) :=
  Equiv.prodCongr σ.symm (Equiv.refl _)

theorem reidx_permIdx (σ : Equiv.Perm (Fin N)) (y : UnitAddTorus (Fin N × Fin d)) :
    reidx (permIdx σ) y = flat (unflat y ∘ σ) := by
  funext q
  rfl

/-- **Weak gradients under label permutations.** If `∇(F ∘ unflat) = G` then
`∇((F(· ∘ σ)) ∘ unflat)_{(i,k)} = G(flat (unflat y ∘ σ))_{(σ⁻¹ i, k)}`. -/
theorem isWeakGrad_perm (σ : Equiv.Perm (Fin N)) {F : Config N d → ℝ}
    {G : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (h : IsWeakGrad (F ∘ unflat) G)
    (hF : Integrable (F ∘ unflat) volume) (hG : ∀ q, Integrable (fun y => G y q) volume) :
    IsWeakGrad ((fun X => F (X ∘ σ)) ∘ unflat)
      (fun y q => G (flat (unflat y ∘ σ)) (σ.symm q.1, q.2)) := by
  have := isWeakGrad_reidx (permIdx σ) h hF hG
  convert this using 2
  · rw [reidx_permIdx]; rfl
  · rw [reidx_permIdx]; rfl

end SharpLSI.FL
