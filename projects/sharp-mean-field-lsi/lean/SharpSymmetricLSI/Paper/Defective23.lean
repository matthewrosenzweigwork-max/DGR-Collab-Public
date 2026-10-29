import SharpSymmetricLSI.Paper.Defective22

/-!
# R03 (Proposition 2.2), part 23: exchangeability of the scores

For a symmetric `Q` with weak gradient `G`, `G(y)_{(i,k)} = G(τy)_{τ(i,k)}` a.e. for every particle
permutation `τ`, so integrals of `(G_{i,·}, X_i, Q)` do not depend on `i`
(`lintegral_block_perm`). Applied to the regularized law: the relative scores `s_i - G_i` have
the same second moment for every particle (`lintegral_sG_eq`).
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The particle permutation acting on flat coordinates. -/
def blockPerm {N : ℕ} (σ : Equiv.Perm (Fin N)) : Fin N × Fin d ≃ Fin N × Fin d :=
  Equiv.prodCongr σ (Equiv.refl _)

theorem unflat_reidx_blockPerm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (y : UnitAddTorus (Fin N × Fin d)) :
    unflat (reidx (blockPerm σ) y) = unflat y ∘ σ.symm := by
  funext i k; simp [unflat, reidx, blockPerm]

theorem lintegral_block_perm {N : ℕ} {F : UnitAddTorus (Fin N × Fin d) → ℝ}
    {G : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hG : IsWeakGrad F G)
    (hFi : Integrable F volume) (hGi : ∀ a, Integrable (fun y => G y a) volume)
    (hsym : ∀ (σ : Equiv.Perm (Fin N)) y, F (reidx (blockPerm σ) y) = F y)
    (Ψ : (Fin d → ℝ) → UnitAddTorus (Fin d) → ℝ → ℝ≥0∞) (i i' : Fin N) :
    ∫⁻ y, Ψ (fun k => G y (i, k)) (projBlock i y) (F y) =
      ∫⁻ y, Ψ (fun k => G y (i', k)) (projBlock i' y) (F y) := by
  set τ := blockPerm (d := d) (Equiv.swap i i')
  have h2 := isWeakGrad_reidx τ hG hFi hGi
  have hF : (fun y => F (reidx τ y)) = F := funext fun y => hsym _ y
  rw [hF] at h2
  have hae := weakGrad_ae_unique hG h2
  have hmp := measurePreserving_reidx_torus τ
  have hemb : MeasurableEmbedding (reidx τ : UnitAddTorus (Fin N × Fin d) → _) := by
    rw [reidx_eq_piCongrLeft]; exact MeasurableEquiv.measurableEmbedding _
  rw [lintegral_congr_ae (g := fun y => Ψ (fun k => G (reidx τ y) (τ (i, k))) (projBlock i y) (F y))
    (hae.mono fun y hy => by simp only [hy])]
  have e : ∀ y, Ψ (fun k => G (reidx τ y) (τ (i, k))) (projBlock i y) (F y) =
      (fun z => Ψ (fun k => G z (i', k)) (projBlock i' z) (F z)) (reidx τ y) := fun y => by
    have hFτ : F (reidx τ y) = F y := hsym _ y
    simp only
    rw [hFτ]
    congr 1
    · funext k; simp [τ, blockPerm]
    · funext k; simp [projBlock, reidx, τ, blockPerm]
  simp_rw [e]
  exact hmp.lintegral_comp_emb hemb (fun z => Ψ (fun k => G z (i', k)) (projBlock i' z) (F z))

theorem Qreg_perm {N : ℕ} {f : Config N d → ℝ} (hsym : IsSymmetric f) (n : ℕ)
    (σ : Equiv.Perm (Fin N)) (X : Config N d) : Qreg V W n f (X ∘ σ) = Qreg V W n f X := by
  unfold Qreg uReg gibbsDensR
  rw [hsym, hamiltonian_perm]

section exch
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  (hsym : IsSymmetric f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ)
include hyp hac hN hfm hf hsym hw hgm hg2 hgi

/-- **Exchangeability**: `E_ν |s_i - G_i|²` does not depend on `i`. -/
theorem lintegral_sG_eq (i i' : Fin N) :
    ∫⁻ X, ENNReal.ofReal (∑ k, (sfun n f g i k X - Gfun W μ i k X) ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      ∫⁻ X, ENNReal.ofReal (∑ k, (sfun n f g i' k X - Gfun W μ i' k X) ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQ0 : ∀ X, 0 < Qreg V W n f X := fun X => hc.trans_le (hb X).1
  set Ψ : (Fin d → ℝ) → UnitAddTorus (Fin d) → ℝ → ℝ≥0∞ := fun v z t =>
    ENNReal.ofReal t * ENNReal.ofReal (∑ k, (v k / t + lipGrad (PhiMF V W μ) z k) ^ 2)
  have key : ∀ (i : Fin N), ∫⁻ X, ENNReal.ofReal (∑ k, (sfun n f g i k X - Gfun W μ i k X) ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      ∫⁻ y, Ψ (fun k => GQreg V W μ n f g y (i, k)) (projBlock i y) (Qreg V W n f (unflat y)) := by
    intro i
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ ((hQm).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    rw [← (measurePreserving_unflat N).lintegral_comp_emb (flatEquiv N d).symm.measurableEmbedding]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply, Ψ]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := GQreg_flat_eq hyp hf (μ := μ) (g := g) n i k (unflat y)
    have hq := hQ0 (unflat y)
    rw [show flat (unflat y) = y from rfl] at h
    rw [h, show unflat y i = projBlock i y from rfl]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  rw [key i, key i']
  refine lintegral_block_perm (isWeakGrad_Qreg hyp hac hN hf hw hgi n) (integrable_Qreg hyp hac hN hfm hf n)
    (fun a => (memLp_GQreg hyp hac hN hfm hf n hg2 a).integrable one_le_two) (fun σ y => ?_) Ψ i i'
  simp only [Function.comp_apply]
  rw [unflat_reidx_blockPerm, Qreg_perm hsym]

end exch

end SharpLSI
