import SharpSymmetricLSI.Paper.Defective6

/-!
# R03 (Proposition 2.2), part 7: weak gradients of the conditional densities

If `Q ∘ unflat` has the integrable weak gradient `GQ`, then for a.e. past `p` the marginal
`margQ p` has the weak gradient `gradMarg p x k = ∫ GQ(assemble p x z)_{(j,k)} dz`
(`ae_isWeakGrad_margQ`): reindex to blocks, integrate out the rest (`isWeakGrad_marginal`), swap
the remaining two blocks and slice in the particle `j` (`isWeakGrad_sliceSum`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

section grad
variable {j : ℕ} (hj : j < N)

/-- The `x`-gradient of the marginal density. -/
noncomputable def gradMarg (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (p : Config j d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ z, GQ (flat (assemble hj p x z)) (⟨j, hj⟩, k) ∂(volume : Measure (Config (N - j - 1) d))

theorem integral_flat_comp {n : ℕ} (g : UnitAddTorus (Fin n × Fin d) → ℝ) :
    ∫ z, g (flat z) ∂(volume : Measure (Config n d)) = ∫ y, g y :=
  (measurePreserving_flat' n).integral_comp measurableEmbedding_flat g

theorem reidx_sumComm_join {X : Type*} {α β : Type*} (x : α → X) (a : β → X) :
    reidx (Equiv.sumComm α β) (join x a) = join a x := by
  funext i; cases i <;> rfl

variable {Q : Config N d → ℝ} {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
  (hQw : IsWeakGrad (Q ∘ unflat) GQ) (hQi : Integrable (Q ∘ unflat) volume)
  (hGi : ∀ k, Integrable (fun y => GQ y k) volume)
include hQw hQi hGi

/-- **For a.e. past, `∇ₓ margQ = gradMarg`.** -/
theorem ae_isWeakGrad_margQ :
    ∀ᵐ p ∂(volume : Measure (Config j d)), IsWeakGrad (margQ hj Q p) (gradMarg hj GQ p) := by
  set σ := blockIdx (d := d) j hj
  have hb := isWeakGrad_reidx σ hQw hQi hGi
  have hbi : Integrable (fun y => (Q ∘ unflat) (reidx σ y)) volume := integrable_comp_reidx σ hQi
  have hbg : ∀ s, Integrable (fun y => GQ (reidx σ y) (σ s)) volume := fun s =>
    integrable_comp_reidx σ (hGi (σ s))
  have hm := isWeakGrad_marginal hb hbi hbg
  set M : UnitAddTorus ((Fin j × Fin d) ⊕ Fin d) → ℝ :=
    fun w => ∫ zf, (Q ∘ unflat) (reidx σ (join w zf)) with hM
  set GM : UnitAddTorus ((Fin j × Fin d) ⊕ Fin d) → ((Fin j × Fin d) ⊕ Fin d) → ℝ :=
    fun w s => ∫ zf, GQ (reidx σ (join w zf)) (σ (Sum.inl s)) with hGM
  have hMi : Integrable M volume := integrable_marginal hbi
  have hGMi : ∀ s, Integrable (fun w => GM w s) volume := fun s => integrable_marginal (hbg _)
  set τ := Equiv.sumComm (Fin d) (Fin j × Fin d)
  have hm' := isWeakGrad_reidx τ hm hMi hGMi
  have hs := isWeakGrad_sliceSum hm' (integrable_comp_reidx τ hMi)
    (fun s => integrable_comp_reidx τ (hGMi (τ s)))
  filter_upwards [(measurePreserving_flat' j).quasiMeasurePreserving.ae hs] with p hp
  convert hp using 1
  · funext x
    rw [reidx_sumComm_join]
    simp only [hM, margQ]
    rw [← integral_flat_comp]
    rfl
  · funext x k
    rw [reidx_sumComm_join]
    simp only [hGM, gradMarg]
    rw [← integral_flat_comp]
    rfl

end grad

end SharpLSI
